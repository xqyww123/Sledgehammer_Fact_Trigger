theory Sledgehammer_Fact_Trigger_Test
  imports Main
begin

text \<open>
  The pieces \<open>PQ\<close>, \<open>QR\<close>, \<open>P7\<close> are hidden from Sledgehammer's pool of facts by \<open>no_atp\<close>, so a
  proof of \<open>R 7\<close> has to use a fact that a trigger generates from them.
\<close>

consts P :: "nat \<Rightarrow> bool" Q :: "nat \<Rightarrow> bool" R :: "nat \<Rightarrow> bool" f :: "nat \<Rightarrow> nat"
  Z :: "int \<Rightarrow> bool"

axiomatization where
  PQ [no_atp]: "P x \<Longrightarrow> Q x" and
  QR [no_atp]: "Q x \<Longrightarrow> R x" and
  P7 [no_atp]: "P 7" and
  PQf [no_atp]: "P x \<Longrightarrow> Q (f x)" and
  QZ: "Q x \<Longrightarrow> Z 0 \<Longrightarrow> R x"

ML \<open>
open Sledgehammer_MePo

fun check name b = if b then () else error ("Failed check: " ^ name)

val goal = \<^prop>\<open>R 7\<close>
val list_goal = \<^prop>\<open>rev (xs @ ys) = rev ys @ rev xs\<close>
(*far from both goals*)
val unrelated = \<^prop>\<open>wf (trancl (Id :: (bool \<times> bool) set))\<close>

fun mepo ctxt max_facts goal =
  let
    val params = Sledgehammer_Commands.default_params (Proof_Context.theory_of ctxt) []
    val (hyp_ts, concl_t) = (Logic.strip_imp_prems goal, Logic.strip_imp_concl goal)
    val facts = Sledgehammer_Fact.nearly_all_facts_of_context ctxt false
      Sledgehammer_Fact.no_fact_override [] hyp_ts concl_t
  in mepo_suggested_facts_with_origin ctxt params max_facts NONE hyp_ts concl_t facts end

fun with_trigger trigger = Context.proof_map (add_trigger "toy" trigger)

fun cand name prop : candidate =
  {name = name, prop = prop, stature = (ATP_Problem_Generate.Global, ATP_Problem_Generate.General)}

fun on_const c cands : trigger = fn {new_consts, ...} =>
  if member (op =) new_consts c then cands else []

(*the generated facts of a result: index, name, proposition*)
fun generated res =
  map_index I res |> map_filter (fn (i, (((name, _), th), From_Trigger)) =>
    SOME (i, name, Thm.prop_of th) | _ => NONE)

fun names_of res = map (fst o fst o fst) res
\<close>


section \<open>Candidates in MePo's result\<close>

ML \<open>
(*generated in a later round: Q becomes relevant only when QZ is accepted*)
val res = mepo (with_trigger (on_const \<^const_name>\<open>Q\<close> [cand "PQ[OF P7]" \<^prop>\<open>Q 7\<close>]) \<^context>) 64 goal
val _ = check "later round"
  (case generated res of [(i, "PQ[OF P7]", t)] => i > 0 andalso t aconv \<^prop>\<open>Q 7\<close> | _ => false)

(*generated before round 0: R occurs in the goal*)
val res = mepo (with_trigger (on_const \<^const_name>\<open>R\<close> [cand "QR[OF PQ[OF P7]]" goal]) \<^context>) 64 goal
val _ = check "before round 0" (map #2 (generated res) = ["QR[OF PQ[OF P7]]"])

(*a candidate that MePo rejects is never evaluated*)
val res = mepo (with_trigger (on_const \<^const_name>\<open>R\<close> [cand "no_such_fact" unrelated]) \<^context>) 64 goal
val _ = check "rejected candidate" (null (generated res))

(*the same proposition from every round and from two expressions: one fact*)
val res = mepo (with_trigger (fn _ =>
  [cand "QR[OF PQ]" (Logic.varify_global \<^prop>\<open>P x \<Longrightarrow> R x\<close>),
   cand "PQ[THEN QR]" (Logic.varify_global \<^prop>\<open>P y \<Longrightarrow> R y\<close>)]) \<^context>) 64 goal
val _ = check "distinct candidates" (map #2 (generated res) = ["QR[OF PQ]"])

(*the kernel renames the schematic variable; the trigger need not predict that*)
val res = mepo (with_trigger (on_const \<^const_name>\<open>R\<close>
  [cand "QR[OF PQf]" (Logic.varify_global \<^prop>\<open>P x \<Longrightarrow> R (f x)\<close>)]) \<^context>) 64 goal
val _ = check "renamed schematic variable" (map #2 (generated res) = ["QR[OF PQf]"])

(*a constant that occurs in no fact of the pool*)
val res = mepo (with_trigger (on_const \<^const_name>\<open>R\<close>
  [cand "QR[OF PQ[OF P7]]" \<^prop>\<open>P 0 \<Longrightarrow> R 7\<close>]) \<^context>) 64 goal
val _ = check "unseen constant" (length (generated res) = 1)

(*the result is cut after the special facts are inserted: tags and facts still agree*)
val res = mepo (with_trigger (on_const \<^const_name>\<open>R\<close> [cand "QR[OF PQ[OF P7]]" goal]) \<^context>) 8
  \<^prop>\<open>R 7 \<and> x \<in> {y. y = (0::nat)}\<close>
val _ = check "cut result"
  (length res = 8 andalso exists (fn (_, origin) => origin = From_Trigger) res andalso
   forall (fn (((name, _), _), origin) => (name = "QR[OF PQ[OF P7]]") = (origin = From_Trigger)) res)

(*facts of the pool are selected as without triggers, although the rejected candidate contains
  many occurrences of a constant of the goal: it is not counted into the pool's frequencies*)
val many_revs =
  \<^Const>\<open>Trueprop for \<^Const>\<open>conj for
    \<open>funpow 2000 (fn t => \<^Const>\<open>rev \<^typ>\<open>bool\<close> for t\<close>) \<^term>\<open>[] :: bool list\<close>
      |> (fn t => HOLogic.mk_eq (t, t))\<close>
    \<open>HOLogic.dest_Trueprop unrelated\<close>\<close>\<close>
val _ = check "pool facts unchanged"
  (names_of (mepo (with_trigger (fn _ => [cand "no_such_fact" unrelated, cand "no_such_fact" many_revs])
      \<^context>) 256 list_goal) =
   names_of (mepo \<^context> 256 list_goal))

(*relevant_facts with MePo alone gives MePo's facts*)
val _ =
  let
    val ctxt = with_trigger (on_const \<^const_name>\<open>R\<close> [cand "QR[OF PQ[OF P7]]" goal]) \<^context>
    val params = Sledgehammer_Commands.default_params \<^theory>
      [("fact_filter", "mepo"), ("learn", "false")]
    val facts = Sledgehammer_Fact.nearly_all_facts_of_context ctxt false
      Sledgehammer_Fact.no_fact_override [] [] goal
    val expected = map fst
      (mepo_suggested_facts_with_origin ctxt params 64 NONE [] goal
        (Sledgehammer_Fact.drop_duplicate_facts facts))
  in
    check "relevant_facts with MePo alone"
      (case Sledgehammer_MaSh.relevant_facts ctxt params "e" 64 Sledgehammer_Fact.no_fact_override
          [] goal facts of
        [("mepo", res)] =>
          eq_list (eq_pair (eq_fst (op =)) Thm.eq_thm) (res, expected) andalso
          exists (fn ((name, _), _) => name = "QR[OF PQ[OF P7]]") res
      | _ => false)
  end
\<close>


section \<open>Errors\<close>

ML \<open>
fun error_of trigger =
  (mepo (with_trigger trigger \<^context>) 64 goal; "")
    handle ERROR msg => Protocol_Message.clean_output msg

val _ = check "undefined fact"
  (String.isPrefix
    "Sledgehammer fact trigger \"toy\": the candidate no_such_fact cannot be evaluated:\nUndefined fact"
    (error_of (on_const \<^const_name>\<open>R\<close> [cand "no_such_fact" goal])))

val msg = error_of (on_const \<^const_name>\<open>R\<close> [cand "QR[OF P7]" goal])
val _ = check "no unifiers"
  (String.isPrefix "Sledgehammer fact trigger \"toy\": the candidate QR[OF P7] cannot be evaluated:\n" msg
   andalso forall (fn s => String.isSubstring s msg) ["OF: no unifiers", "Q ?x \<Longrightarrow> R ?x", "P 7"])

val _ = check "two theorems"
  (error_of (on_const \<^const_name>\<open>R\<close> [cand "PQ QR" goal]) =
    "Sledgehammer fact trigger \"toy\": the candidate PQ QR evaluates to 2 theorems, but exactly one is expected.")

(*an exception of the trigger itself passes through*)
val _ = check "exception of the trigger"
  ((mepo (with_trigger (fn _ => [the NONE]) \<^context>) 64 goal; false) handle Option.Option => true)
\<close>


section \<open>Merging with other fact filters\<close>

ML \<open>
local
  open Sledgehammer_MaSh
  val with_generated = mepo (with_trigger (on_const \<^const_name>\<open>Q\<close> [cand "PQ[OF P7]" \<^prop>\<open>Q 7\<close>]) \<^context>) 64 goal
  val plain = mepo \<^context> 64 goal
  (*another fact filter, which never lists the generated fact*)
  val other = weight_facts_steeply (rev (map fst plain))
  fun index_in facts = find_index (fn ((name, _), _) => name = "PQ[OF P7]") facts
  val stock_mesh =
    mesh_facts (Sledgehammer_Fact.fact_distinct (op aconv)) (eq_snd Thm.eq_thm_prop) 64
  val mepo_index = index_in (map fst with_generated)
  val eq_facts = eq_list (eq_snd Thm.eq_thm)
in
  val _ = check "generated fact keeps its rank"
    (mepo_index > 0 andalso
     let val i = index_in (mesh_facts_with_mepo \<^context> 64 (0.5, with_generated) [(0.5, (other, []))])
     in 0 <= i andalso i <= mepo_index end
     andalso
     index_in (stock_mesh
       [(0.5, (weight_facts_steeply (map fst with_generated), [])), (0.5, (other, []))]) > mepo_index)
  val _ = check "inserted at the index of MePo"
    (index_in (insert_generated_facts with_generated (map fst other)) = mepo_index)
  val _ = check "no generated fact: as mesh_facts"
    (eq_facts (mesh_facts_with_mepo \<^context> 64 (0.5, plain) [(0.5, (other, []))],
       stock_mesh [(0.5, (weight_facts_steeply (map fst plain), [])), (0.5, (other, []))])
     andalso eq_facts (insert_generated_facts plain (map fst other), map fst other))
end
\<close>


section \<open>Proofs that name a generated fact\<close>

lemma "R 7"
  by (metis QR["OF" PQ [ OF P7 ]])

ML \<open>
(*Try0 prints nested attributes as text that Isar parses*)
val xref = Sledgehammer_Util.xref_of_name \<^context> "QR[OF PQ[OF P7]]"
val _ = check "text of nested attributes"
  (Try0_Util.string_of_xref' \<^context> xref = "QR[\"OF\" PQ [ OF P7 ]]")

(*a name that Sledgehammer quotes is printed with its quotes*)
val _ = check "text of a quoted name"
  (Try0_Util.string_of_xref' \<^context> (Sledgehammer_Util.xref_of_name \<^context> "\"1.IH\"(2)") =
    "\"1.IH\"(2)")

(*every form of a fact reference is printed as text that is parsed back to the same reference:
  printing the parsed text again gives the same text*)
val _ =
  ["PQ", "Sledgehammer_Fact_Trigger_Test.PQ", "PQ(1)", "\"1.IH\"(2)", "\"\"(1)", "PQ[OF P7]",
   "QR[OF PQ[OF P7]]", "PQ[of 7, OF P7]", "QR[OF PQ, of 7, OF P7]",
   "QR[OF PQ[of 7, OF P7], simplified]", "PQ[where x = 7, THEN QR]", "PQ[of \"Suc 6\"]",
   "[[simp]]", "[[]]", "\<open>P 7 \<Longrightarrow> Q 7\<close>", "\<open>P 7 \<Longrightarrow> Q 7\<close>[OF P7]"]
  |> List.app (fn name =>
    let
      val print = Try0_Util.string_of_xref' \<^context> o Sledgehammer_Util.xref_of_name \<^context>
      val text = print name
    in check ("round trip of " ^ name ^ ", printed as " ^ text) (print text = text) end)

(*several attributes are one list; the anonymous fact has its own brackets*)
val _ = check "text of several attributes"
  (Try0_Util.string_of_xref' \<^context> (Sledgehammer_Util.xref_of_name \<^context> "PQ[of 7, OF P7]") =
    "PQ[\"of\" 7, \"OF\" P7]")
val _ = check "text of the anonymous fact"
  (Try0_Util.string_of_xref' \<^context> (Sledgehammer_Util.xref_of_name \<^context> "[[simp]]") =
    "[[\"simp\"]]")
val _ = check "the same theorem from the printed text"
  (eq_list Thm.eq_thm
    (apply2 (fn name =>
        Attrib.eval_thms \<^context> [Sledgehammer_Util.xref_of_name \<^context> name])
      ("QR[OF PQ, of 7, OF P7]", "QR[\"OF\" PQ, \"of\" 7, \"OF\" P7]")))

fun try0 meth facts =
  Try0.get_proof_method_or_noop meth (SOME (seconds 10.0)) facts
    (Proof.theorem NONE (K I) [[(goal, [])]] \<^context>)
  |> Option.map (Protocol_Message.clean_output o #command)
val _ = check "try0 metis"
  (try0 "metis" {usings = [], directs = [xref], simps = [], intros = [], elims = [], dests = []} =
    SOME "by (metis QR[\"OF\" PQ [ OF P7 ]])")
val _ = check "try0 simp"
  (try0 "simp" {usings = [xref], directs = [], simps = [], intros = [], elims = [], dests = []} =
    SOME "using QR[\"OF\" PQ [ OF P7 ]] by simp")
\<close>

ML \<open>
(*Sledgehammer finds a proof that uses the generated fact; for an automatic prover, a one-line
  proof with that fact is preplayed.  A prover is skipped where it is not installed.*)
fun hammer (prover, preplayed, name) =
  let
    val ctxt = with_trigger (on_const \<^const_name>\<open>R\<close> [cand name goal]) \<^context>
    val state = Proof.theorem NONE (K I) [[(goal, [])]] ctxt
    val params = Sledgehammer_Commands.default_params \<^theory>
      [("provers", prover), ("learn", "false"), ("timeout", "60"), ("preplay_timeout", "10")]
    val (_, (outcome, _)) =
      Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Normal (SOME (K ())) 1
        Sledgehammer_Fact.no_fact_override state
  in
    check ("sledgehammer with " ^ prover ^ " and " ^ name)
      (not (Sledgehammer_Prover_Minimize.is_prover_installed ctxt prover) orelse
       (case outcome of
         Sledgehammer.SH_Some ({used_facts, ...}, preplay_results) =>
           AList.defined (op =) used_facts name andalso
           (not preplayed orelse
            exists (fn (_, (Sledgehammer_Proof_Methods.Played _, _)) => true | _ => false)
              preplay_results)
       | _ => false))
  end
val _ = List.app hammer
  [("e", true, "QR[OF PQ[OF P7]]"), ("cvc5", true, "QR[OF PQ[OF P7]]"),
   ("metis", false, "QR[OF PQ[OF P7]]"),
   (*several attributes: metis parses the text that Try0 prints for the fact*)
   ("metis", false, "QR[OF PQ, of 7, OF P7]")]
\<close>

end
