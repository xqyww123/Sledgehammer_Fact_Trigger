theory Fact_Reference_Test
  imports Main
begin

text \<open>
  The text that Sledgehammer and Metis give for a fact reference is read back by Isar as that
  very fact.
\<close>

consts P :: "nat \<Rightarrow> bool" Q :: "nat \<Rightarrow> bool" R :: "nat \<Rightarrow> bool"

axiomatization where
  PQ: "P x \<Longrightarrow> Q x" and QR: "Q x \<Longrightarrow> R x" and P7: "P 7" and
  P1: "P 1" and P2: "P 2" and P3: "P 3" and P4: "P 4"

lemmas four = P1 P2 P3 P4
lemmas imps = PQ QR

ML \<open>
fun check name b = if b then () else error ("Failed check: " ^ name)

fun evaluates_to ctxt th name =
  eq_list Thm.eq_thm (Sledgehammer_Util.thms_of_name ctxt name, [th]) handle ERROR _ => false
\<close>


section \<open>The names of the facts listed in a Sledgehammer invocation\<close>

ML \<open>
fun facts_of ctxt text =
  Sledgehammer_Fact.fact_of_ref ctxt (Thy_Header.get_keywords' ctxt) []
    (Sledgehammer_Fact.clasimpset_rule_table_of ctxt) (Sledgehammer_Util.xref_of_name ctxt text)

fun names_of ctxt text = map (fst o fst) (facts_of ctxt text)

(*a selection is expanded by the length of the whole fact*)
val _ = check "indexes of (3-, 1) among 4"
  (Try0_Util.indexes_of_selection 4 [Facts.From 3, Facts.Single 1] = [3, 4, 1])

(*the names, in the order in which the reference yields its theorems*)
val _ =
  [("PQ", ["PQ"]),
   ("four", ["four(1)", "four(2)", "four(3)", "four(4)"]),
   ("four(3-, 1)", ["four(3)", "four(4)", "four(1)"]),
   ("four(2-3)", ["four(2)", "four(3)"]),
   ("imps[of 7]", ["imps(1)[\"of\" 7]", "imps(2)[\"of\" 7]"]),
   ("imps(2-, 1)[of 7]", ["imps(2)[\"of\" 7]", "imps(1)[\"of\" 7]"]),
   ("PQ[of 7, OF P7]", ["PQ[\"of\" 7, \"OF\" P7]"]),
   ("[[simp]]", ["[[\"simp\"]]"]),
   ("[[]]", ["[[]]"])]
  |> List.app (fn (text, names) =>
    check ("names of " ^ text) (names_of \<^context> text = names))

(*each name denotes its theorem*)
val _ =
  ["PQ", "four", "four(3-, 1)", "imps[of 7]", "imps(2-, 1)[of 7]", "imps(1)[of 7, OF P7]",
   "PQ[of 7, OF P7]", "[[simp]]", "[[]]"]
  |> List.app (fn text =>
    check ("facts of " ^ text)
      (forall (fn ((name, _), th) => evaluates_to \<^context> th name) (facts_of \<^context> text)))
\<close>

text \<open>A literal fact keeps the blanks inside a string and has no control characters.\<close>

lemma True
proof -
  have "length ''a  b'' = 4" by simp
  ML_val \<open>
    val [((name, _), th)] = facts_of \<^context> "\<open>length ''a  b'' = 4\<close>[symmetric]"
    val _ = check ("literal fact " ^ name)
      (name = "\<open>length ''a  b'' = 4\<close>[\"symmetric\"]" andalso evaluates_to \<^context> th name)
  \<close>
  show True ..
qed


section \<open>Attributes added to a name\<close>

ML \<open>
val add = Sledgehammer_Util.add_attribs_to_name \<^context>

(*a name without attributes keeps its text*)
val _ =
  ["nat.induct", "four(2)", "\"1.IH\"(2)", "\<open>P 7\<close>"]
  |> List.app (fn name =>
    check ("attributes added to " ^ name)
      (add "where P = \"x\"" name = name ^ "[where P = \"x\"]"))

(*a name with attributes gets one list*)
val _ = check "attributes merged"
  (add "where P = \"x\"" "nat.induct[case_names Z S]" =
    "nat.induct[\"case_names\" Z S, \"where\" P = \"x\"]")
val _ = check "merged attributes denote the instance"
  (eq_list Thm.eq_thm
    (apply2 (Sledgehammer_Util.thms_of_name \<^context>)
      (add "where P = \"\<lambda>n. n + 0 = n\"" "nat.induct[case_names Z S]",
       "nat.induct[where P = \"\<lambda>n. n + 0 = n\"]")))

(*text that is not parsed is appended as before*)
val _ = check "attributes that are not parsed"
  (add "where P = \"a\"b\"" "foo[a]" = "foo[a][where P = \"a\"b\"]")
\<close>


section \<open>The names that Metis gives to its theorems\<close>

ML \<open>
(*the arguments of a metis call as its parser sees them: the tokens carry their values*)
fun metis_args ctxt text =
  let val (_, src) = Method.read_closure_input ctxt (Input.string ("metis " ^ text)) in
    Scan.finite' Token.stopper (Scan.repeat ATP_Util.scan_and_trace_multi_thm)
      (Context.Proof ctxt, Token.args_of_src src)
    |> fst
  end

fun metis_names ctxt text =
  let val args = metis_args ctxt text in
    maps (fn (ths, toks) =>
      (check ("the name token of " ^ text ^ " has its value")
        (case Token.get_value (hd toks) of SOME (Token.Fact _) => true | _ => false);
       map (fn th => (Metis_Tactic.th_name_of_multi_thms ctxt args th, th)) ths)) args
  end

val _ =
  [("four", ["four(1)", "four(2)", "four(3)", "four(4)"]),
   ("four(3-, 1)", ["four(3)", "four(4)", "four(1)"]),
   ("four(1 - 2)", ["four(1)", "four(2)"]),
   ("imps[of 7]", ["imps(1)[of 7]", "imps(2)[of 7]"]),
   ("imps(2-, 1)[of 7, simplified]", ["imps(2)[of 7,simplified]", "imps(1)[of 7,simplified]"]),
   ("PQ[of \"length ''a  b''\"]", ["PQ[of \"length ''a  b''\"]"]),
   ("imps[of \"length ''a, b''\"]",
    ["imps(1)[of \"length ''a, b''\"]", "imps(2)[of \"length ''a, b''\"]"]),
   ("PQ QR", ["PQ", "QR"])]
  |> List.app (fn (text, names) =>
    let val named = metis_names \<^context> text in
      check ("metis names of " ^ text)
        (map fst named = map SOME names andalso
         forall (fn (name, th) => evaluates_to \<^context> th (the name)) named)
    end)
\<close>

text \<open>A fact that is not an argument is named only by a name that denotes it.\<close>

lemma True
proof -
  have a: "P 5 \<Longrightarrow> Q 5" by (rule PQ)
  note PQ = QR
  ML_val \<open>
    val name_of = Metis_Tactic.th_name_of_multi_thms \<^context> []
    val _ = check "a local fact" (name_of @{thm a} = SOME "a")
    val _ = check "a fact made by an attribute" (name_of @{thm QR[OF a]} = NONE)
    val _ = check "an instance" (name_of @{thm imps(1)[of 7]} = NONE)
    val _ = check "a member of a fact" (name_of @{thm four(2)} = SOME "four(2)")
    val _ = check "a global fact" (name_of @{thm P7} = SOME "P7")
    val _ = check "a global fact hidden by a local one"
      (name_of (Global_Theory.get_thm \<^theory> "Fact_Reference_Test.PQ") =
        SOME "Fact_Reference_Test.PQ")
    val _ = check "a name hint for another theorem"
      (name_of (Thm.put_name_hint ("Fact_Reference_Test.P7", 0) @{thm QR}) = NONE)
  \<close>
  show True ..
qed

text \<open>Metis calls that print names: the unused theorems, and the instantiations.\<close>

declare [[metis_instantiate]]

lemma "R 7"
  by (metis imps P7 four(3-, 1))

lemma
  assumes a: "\<And>x. P x \<Longrightarrow> Q x"
  shows "Q 7"
  using a P7[THEN PQ, THEN QR] by (metis P7 imps(2-, 1))

end
