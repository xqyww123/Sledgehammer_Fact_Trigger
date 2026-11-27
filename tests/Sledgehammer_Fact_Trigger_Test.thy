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

val stature = (ATP_Problem_Generate.Global, ATP_Problem_Generate.General)

(*a candidate whose theorem is what its name denotes here*)
fun cand name prop : candidate =
  {name = K name,
   thm = Lazy.lazy (fn () => the_single (Sledgehammer_Util.thms_of_name \<^context> name)),
   prop = prop, stature = stature}

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

(*the theorem of an accepted candidate is the one that the trigger hands over, whatever its name
  says: the text of the name is not evaluated, be it no fact or another fact*)
val _ = ["no_such_fact", "QR[OF PQ[OF P7]]"] |> List.app (fn name =>
  let
    val res = mepo (with_trigger (on_const \<^const_name>\<open>R\<close>
      [{name = K name, thm = Lazy.value @{thm PQ[OF P7]}, prop = goal, stature = stature}])
      \<^context>) 64 goal
  in
    check ("the theorem that the trigger hands over " ^ name)
      (case generated res of
        [(_, name', t)] => name' = name andalso t aconv \<^prop>\<open>Q 7\<close>
      | _ => false)
  end)

(*of a candidate that MePo rejects, neither the theorem is forced nor the name printed*)
val res = mepo (with_trigger (on_const \<^const_name>\<open>R\<close>
  [{name = fn () => error "The name is printed", thm = Lazy.lazy (fn () => error "The theorem is forced"),
    prop = unrelated, stature = stature}]) \<^context>) 64 goal
val _ = check "rejected candidate" (null (generated res))

(*so does a candidate that the quota cuts: with room for one fact, of two candidates of the
  highest score exactly one has its theorem forced, and at most one its name printed*)
val forced = Synchronized.var "forced" (0: int)
val named = Synchronized.var "named" (0: int)
fun counted name th prop : candidate =
  {name = fn () => (Synchronized.change named (fn n => n + 1); name),
   thm = Lazy.lazy (fn () => (Synchronized.change forced (fn n => n + 1); th)),
   prop = prop, stature = stature}
val _ = mepo (with_trigger (on_const \<^const_name>\<open>R\<close>
  [counted "QR[OF PQ[OF P7]]" @{thm QR[OF PQ[OF P7]]} goal,
   counted "TrueI" @{thm TrueI} \<^prop>\<open>R 7 \<Longrightarrow> R 7\<close>]) \<^context>) 1 goal
val _ = check "candidate cut by the quota"
  (Synchronized.value forced = 1 andalso Synchronized.value named <= 1)

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

(*an exception raised while the theorem of an accepted candidate is forced passes through as it
  is*)
val _ = check "exception of the theorem"
  (String.isPrefix "Undefined fact"
    (error_of (on_const \<^const_name>\<open>R\<close> [cand "no_such_fact" goal])))

(*also one that is not an ERROR*)
val _ = check "exception of the theorem that is no error"
  ((mepo (with_trigger (on_const \<^const_name>\<open>R\<close>
      [{name = K "QR[OF PQ[OF P7]]", thm = Lazy.lazy (fn () => the NONE), prop = goal,
        stature = stature}]) \<^context>) 64 goal; false)
    handle Option.Option => true)

(*so does one raised while the name of an accepted candidate is printed: MePo prints the names of
  the facts that it returns*)
val _ = check "exception of the name"
  (error_of (on_const \<^const_name>\<open>R\<close>
    [{name = fn () => error "The name is printed", thm = Lazy.value @{thm QR[OF PQ[OF P7]]},
      prop = goal, stature = stature}]) = "The name is printed")

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

ML \<open>
(*the fact lists that relevant_facts gives for the results of MePo and MaSh*)
local
  open Sledgehammer_MaSh
  val stature = (ATP_Problem_Generate.Global, ATP_Problem_Generate.General)
  fun fact name th : Sledgehammer_Fact.fact = ((name, stature), th)
  val (f1, f2, f3) = (fact "PQ" @{thm PQ}, fact "QR" @{thm QR}, fact "QZ" @{thm QZ})
  val generated = fact "QR[OF PQ[OF P7]]" @{thm QR[OF PQ[OF P7]]}
  val mepo_result = [(f1, From_Pool), (generated, From_Trigger), (f2, From_Pool)]
  val mash_result = (weight_facts_steeply [f3, f2, f1], [])
  fun lists fact_filter effective_fact_filter results =
    facts_of_filter_results \<^context> 64 fact_filter effective_fact_filter results
    |> map (apsnd (map (fst o fst)))
  val three = lists NONE "mesh" (SOME mepo_result, SOME mash_result)
  val in_mepo = ["PQ", "QR[OF PQ[OF P7]]", "QR"]
in
  val _ = check "three lists" (map fst three = ["mesh", "mepo", "mash"])
  val _ = check "the list of MePo" (AList.lookup (op =) three "mepo" = SOME in_mepo)
  val _ = check "the list of MaSh, with the generated fact at its MePo index"
    (AList.lookup (op =) three "mash" = SOME ["QZ", "QR[OF PQ[OF P7]]", "QR", "PQ"])
  val _ = check "the meshed list"
    (eq_set (op =) (the (AList.lookup (op =) three "mesh"), "QZ" :: in_mepo))
  val _ = check "fact_filter = mesh"
    (lists (SOME "mesh") "mesh" (SOME mepo_result, SOME mash_result) =
      [("mesh", the (AList.lookup (op =) three "mesh"))])
  val _ = check "MePo alone" (lists NONE "mepo" (SOME mepo_result, NONE) = [("mepo", in_mepo)])
  val _ = check "fact_filter = mash"
    (lists (SOME "mash") "mash" (NONE, SOME mash_result) = [("mash", ["QZ", "QR", "PQ"])])
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


section \<open>The input of a trigger\<close>

ML \<open>
(*several triggers all run; a trigger registered under the name of another replaces it*)
val two_triggers =
  Context.proof_map
    (add_trigger "a" (on_const \<^const_name>\<open>R\<close> [cand "QR[OF PQ[OF P7]]" goal]) #>
     add_trigger "b" (on_const \<^const_name>\<open>Q\<close> [cand "PQ[OF P7]" \<^prop>\<open>Q 7\<close>])) \<^context>
val _ = check "two triggers"
  (eq_set (op =) (map #2 (generated (mepo two_triggers 64 goal)), ["QR[OF PQ[OF P7]]", "PQ[OF P7]"]))
val _ = check "a replaced trigger"
  (map #2 (generated (mepo (Context.proof_map (add_trigger "a" (K [])) two_triggers) 64 goal)) =
    ["PQ[OF P7]"])

(*what a trigger is given, call by call*)
val inputs = Synchronized.var "inputs" ([] : trigger_input list)
val _ =
  mepo (with_trigger (fn input => (Synchronized.change inputs (cons input); [])) \<^context>) 64
    \<^prop>\<open>P 3 \<Longrightarrow> R 7\<close>
val calls = rev (Synchronized.value inputs)
fun accepted_names ({accepted, ...} : trigger_input) = map (fn ((name, _), _) => name ()) accepted
val _ = writeln (cat_lines (map (fn call as {new_consts, ...} =>
  "new_consts: " ^ commas new_consts ^ "; accepted: " ^ commas (take 5 (accepted_names call)))
  calls))
val _ = check "a call before the first round and one before each later round" (length calls >= 2)
val _ = check "the goal"
  (forall (fn {hyp_ts, concl_t, ...} => hyp_ts = [\<^prop>\<open>P 3\<close>] andalso concl_t aconv goal) calls)
val _ = check "before the first round"
  (case calls of
    (call as {new_consts, rel_consts, ...}) :: _ =>
      null (accepted_names call) andalso
      eq_set (op =) (new_consts, Symtab.keys rel_consts) andalso
      subset (op =) ([\<^const_name>\<open>P\<close>, \<^const_name>\<open>R\<close>], new_consts)
  | [] => false)
val _ = check "later rounds: the accepted facts, most recent first"
  (forall (fn (earlier, later) =>
      is_prefix (op =) (rev (accepted_names earlier)) (rev (accepted_names later)) andalso
      length (accepted_names earlier) < length (accepted_names later))
    (take (length calls - 1) calls ~~ tl calls) andalso
   member (op =) (accepted_names (List.last calls)) "QZ")
val _ = check "later rounds: new_consts are in rel_consts"
  (forall (fn {new_consts, rel_consts, ...} => forall (Symtab.defined rel_consts) new_consts) calls
   andalso exists (fn {new_consts, ...} => member (op =) new_consts \<^const_name>\<open>Q\<close>) (tl calls))
\<close>


section \<open>Sledgehammer with a generated fact\<close>

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

text \<open>
  The tactic provers of Sledgehammer, through \<open>Sledgehammer.run_sledgehammer\<close>: the messages of a run
  that proves the given subgoal with the facts of the triggers \<open>cands\<close>.
\<close>

ML \<open>
fun hammer_messages overrides cands subgoal props =
  let
    val ctxt = with_trigger (on_const \<^const_name>\<open>R\<close> cands) \<^context>
    val state = Proof.theorem NONE (K I) [map (rpair []) props] ctxt
    val params = Sledgehammer_Commands.default_params \<^theory>
      ([("learn", "false"), ("timeout", "60")] @ overrides)
    val messages = Synchronized.var "messages" ([] : string list)
    val _ =
      Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Normal
        (SOME (fn msg => Synchronized.change messages (cons (Protocol_Message.clean_output msg))))
        subgoal Sledgehammer_Fact.no_fact_override state
  in rev (Synchronized.value messages) end

(*all pieces in one message: the minimizer may leave a fact that is not needed in the using
  clause*)
fun shows texts = exists (fn msg => forall (fn text => String.isSubstring text msg) texts)

(*no test of this session loads or changes a MaSh state*)
val _ = check "MaSh is off" (not (Sledgehammer_MaSh.is_mash_enabled ()))

(*auto and fastforce take the generated fact, which is global, by "using"*)
val _ =
  ["auto", "fastforce"] |> List.app (fn prover =>
    check ("sledgehammer with " ^ prover)
      (shows ["using ", "QR[\"OF\" PQ [ OF P7 ]]", " by " ^ prover]
        (hammer_messages [("provers", prover)] [cand "QR[OF PQ[OF P7]]" goal] 1 [goal])))

(*a tactic prover works on the subgoal that it is asked for*)
val _ = check "sledgehammer on subgoal 2"
  (shows ["prefer 2 using ", "QR[\"OF\" PQ [ OF P7 ]]", " apply simp"]
    (hammer_messages [("provers", "simp")] [cand "QR[OF PQ[OF P7]]" goal] 2 [\<^prop>\<open>True\<close>, goal]))

(*instantiations are asked for and the one-line proof with them is not played: the command that
  Try0 ran is shown*)
val _ = check "sledgehammer with instantiate and no preplay"
  (shows ["using ", "QR[\"OF\" PQ]", " by simp"]
    (hammer_messages [("provers", "simp"), ("instantiate", "true"), ("preplay_timeout", "0")]
      [cand "QR[OF PQ]" (Logic.varify_global \<^prop>\<open>P x \<Longrightarrow> R x\<close>)] 1 [\<^prop>\<open>P 7 \<Longrightarrow> R 7\<close>]))
\<close>

end
