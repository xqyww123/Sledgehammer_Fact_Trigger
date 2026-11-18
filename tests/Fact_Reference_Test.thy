theory Fact_Reference_Test
  imports Main
begin

text \<open>
  The text that Sledgehammer and Metis give for a fact reference is read back by Isar as that
  very fact; a tactic prover of Sledgehammer works on the subgoal it is asked for and shows the
  command that was run.
\<close>

consts P :: "nat \<Rightarrow> bool" Q :: "nat \<Rightarrow> bool" R :: "nat \<Rightarrow> bool"
  a :: nat b :: nat c :: nat g :: "nat \<Rightarrow> nat"

axiomatization where
  PQ: "P x \<Longrightarrow> Q x" and QR: "Q x \<Longrightarrow> R x" and P7: "P 7" and
  P1: "P 1" and P2: "P 2" and P3: "P 3" and P4: "P 4" and
  ab: "a = b" and gac: "g a = c"

lemmas four = P1 P2 P3 P4
lemmas imps = PQ QR
lemmas two = ab gac

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


section \<open>Facts of several theorems, unnamed facts, instances\<close>

ML \<open>
val stature = (ATP_Problem_Generate.Global, ATP_Problem_Generate.General)
val clean = Protocol_Message.clean_output
\<close>

subsection \<open>A fact of several theorems with attributes that declare into the context\<close>

ML \<open>
(*the whole reference gives "g b = c" as its second theorem: simplified by the first one*)
val _ = check "the whole reference"
  (map Thm.prop_of (Attrib.eval_thms \<^context> [Sledgehammer_Util.xref_of_name \<^context> "two[simplified, simp]"]) =
    [\<^prop>\<open>a = b\<close>, \<^prop>\<open>g b = c\<close>])

val _ =
  let val facts = facts_of \<^context> "two[simplified, simp]" in
    check ("names " ^ commas (map (fst o fst) facts)) (length facts = 2);
    check "each name denotes its theorem"
      (forall (fn ((name, _), th) => evaluates_to \<^context> th name) facts);
    check "the theorems" (map (Thm.prop_of o snd) facts = [\<^prop>\<open>a = b\<close>, \<^prop>\<open>g a = c\<close>])
  end

(*without attributes, and with attributes that declare nothing: as before*)
val _ =
  ["four", "four(3-, 1)", "imps[of 7]", "imps(2-, 1)[of 7]", "two", "two(2)[symmetric]", "nothing",
   "nothing[simp]"]
  |> List.app (fn text =>
    check ("the theorems of " ^ text)
      (eq_list Thm.eq_thm (map snd (facts_of \<^context> text),
        Attrib.eval_thms \<^context> [Sledgehammer_Util.xref_of_name \<^context> text])))
\<close>

subsection \<open>Blanks inside a string\<close>

lemma True
proof -
  have "length ''a  b'' = 4" by simp
  ML_val \<open>
    val th = @{thm this}
    val name = Sledgehammer_Fact.cartouche_thm \<^context> th
    val _ = check ("the name of an unnamed fact: " ^ name)
      (name = "\<open>length ''a  b'' = 4\<close>")
    val facts =
      Sledgehammer_Fact.nearly_all_facts_of_context \<^context> false
        Sledgehammer_Fact.no_fact_override [] [] \<^prop>\<open>True\<close>
      |> map Sledgehammer_Fact.fact_of_lazy_fact
    val _ = check "among the facts of the context"
      (exists (fn ((name', _), th') => name' = name andalso Thm.eq_thm (th, th')) facts)
  \<close>
  have "length ''a  b'' = 4 \<and> (\<forall>xs ys zs. map Suc (xs @ ys @ zs) = map Suc xs @ map Suc ys @ map Suc zs \<and>
    length (map Suc (xs @ ys @ zs)) = length xs + length ys + length zs \<and>
    rev (map Suc (xs @ ys)) = rev (map Suc ys) @ rev (map Suc xs))" by simp
  ML_val \<open>
    val th = @{thm this}
    val name = Sledgehammer_Fact.cartouche_thm \<^context> th
    val _ = check ("a long proposition: " ^ name)
      (name = "\<open>length ''a  b'' = 4 \<and> (\<forall>xs ys zs. map Suc (xs @ ys @ zs) = \
        \map Suc xs @ map Suc ys @ map Suc zs \<and> length (map Suc (xs @ ys @ zs)) = \
        \length xs + length ys + length zs \<and> rev (map Suc (xs @ ys)) = \
        \rev (map Suc ys) @ rev (map Suc xs))\<close>")
  \<close>
  show True ..
qed

ML \<open>
val _ =
  let
    val concl = \<^prop>\<open>length ''a  b'' + n = n + 4\<close>
    fun instances () =
      Sledgehammer_Fact.instantiate_inducts \<^context> [] concl
        [((K "nat.induct", stature), @{thm nat.induct})]
      |> map Sledgehammer_Fact.fact_of_lazy_fact
      |> filter (fn ((name, _), _) => name <> "nat.induct")
    (*Sledgehammer gives up an instantiation after 0.01 s, times the timeout_scale of the session;
      an instantiation that fails gives no instance either*)
    val insts = get_first (fn _ => (case instances () of [] => NONE | insts => SOME insts)) (1 upto 100)
  in
    check "an instance of nat.induct" (is_some insts);
    check "the predicate keeps the blanks"
      (forall (fn (_, th) =>
        exists_subterm (fn t => t aconv HOLogic.mk_string "a  b") (Thm.prop_of th)) (these insts));
    check ("the name of the instance: " ^ commas (map (fst o fst) (these insts)))
      (map (fst o fst) (these insts) =
        ["nat.induct[where P = \"\<lambda>n. length ''a  b'' + n = n + 4\"]"])
  end
\<close>

subsection \<open>Instantiations added to a name\<close>

ML \<open>
val _ =
  let
    fun inst name =
      Metis_Tactic.pretty_name_inst \<^context> (name, [\<^cterm>\<open>x :: nat\<close>])
      |> Pretty.unformatted_string_of |> clean
  in
    [("[[]]", "[[of x]]"), ("[[simp]]", "[[simp, of x]]"), ("[[ ]]", "[[of x]]"),
     ("foo[OF bar[of y]]", "foo[OF bar[of y], of x]"), ("foo", "foo[of x]"),
     ("foo(2)", "foo(2)[of x]"), ("\<open>P 7\<close>", "\<open>P 7\<close>[of x]"), ("foo[a] ", "foo[a, of x]")]
    |> List.app (fn (name, text) =>
      check (quote name ^ " ==> " ^ inst name) (inst name = text))
  end
val _ = check "no instantiation"
  (clean (Pretty.unformatted_string_of (Metis_Tactic.pretty_name_inst \<^context> ("[[simp]]", []))) =
    "[[simp]]")
\<close>

subsection \<open>Inferring instantiations for a name that cannot be evaluated\<close>

ML \<open>
val _ =
  let
    val state = Proof.theorem NONE (K I) [[(\<^prop>\<open>Q 7\<close>, [])]] \<^context>
    fun insts names =
      Sledgehammer_Instantiations.instantiate_facts state false (seconds 5.0)
        (#goal (Proof.goal state)) 1 (map (rpair stature) names)
      |> Option.map (map (clean o Pretty.unformatted_string_of o fst))
  in
    check "a name that cannot be evaluated"
      ((insts ["PQ", "P7", "\<open>no such fact\<close>"] = NONE) handle ERROR _ => false);
    check ("names that can: " ^ commas (these (insts ["PQ", "P7"])))
      (insts ["PQ", "P7"] = SOME ["PQ[of \"7\"]", "P7"])
  end
\<close>

subsection \<open>Tactic provers: the subgoal, and the command that is shown\<close>

ML \<open>
local
  open Sledgehammer_Prover Sledgehammer_Proof_Methods
  fun run' chained name subgoal props facts =
    let
      val state = Proof.theorem NONE (K I) [map (rpair []) props] \<^context>
        |> not (null chained) ? Proof.using [[(chained, [])]]
      val params = Sledgehammer_Commands.default_params \<^theory> [("timeout", "30")]
      val problem : prover_problem =
        {comment = "", state = state, goal = #goal (Proof.goal state), subgoal = subgoal,
         subgoal_count = Sledgehammer_Util.subgoal_count state, factss = [("mesh", facts)],
         has_already_found_something = K false, found_something = K (),
         memoize_fun_call = (fn f => f)}
    in
      (#subgoal_count problem,
       Sledgehammer_Prover_Tactic.run_tactic_prover Normal name params problem
         ((1, false, false, length facts, "mesh"), No_Slice))
    end
  val run = run' []
  val generated : Sledgehammer_Fact.fact = (("QR[OF PQ[OF P7]]", stature), @{thm QR[OF PQ[OF P7]]})
  fun text preplay ({message, ...} : prover_result) = clean (message preplay)
  fun preplay' outcome meth = SOME ([(Pretty.str "QR[OF PQ[OF P7]]", stature)], (meth, outcome))
  val preplay = preplay' (Played Time.zeroTime)
in
  val (n, res) = run "simp" 2 [\<^prop>\<open>True\<close>, \<^prop>\<open>R 7\<close>] [generated]
  val _ = check ("subgoal 2 of " ^ string_of_int n ^ ": " ^ text NONE res)
    (n = 2 andalso is_none (#outcome res) andalso
     String.isSubstring "prefer 2 using QR[\"OF\" PQ [ OF P7 ]] apply simp" (text NONE res))
  val (_, res) = run "simp" 2 [\<^prop>\<open>Q 99\<close>, \<^prop>\<open>R 7\<close>] [generated]
  val _ = check ("the first subgoal is not provable: " ^ text NONE res) (is_none (#outcome res))
  val (_, res) = run "simp" 1 [\<^prop>\<open>R 7\<close>, \<^prop>\<open>True\<close>] [generated]
  val _ = check ("subgoal 1 of 2: " ^ text NONE res)
    (is_none (#outcome res) andalso not (String.isSubstring "prefer" (text NONE res)))
  (*auto cannot prove subgoal 2: release 3 took the proof of subgoal 1 for it*)
  val (_, res) = run "auto" 2 [\<^prop>\<open>True\<close>, \<^prop>\<open>R 7\<close>, \<^prop>\<open>True\<close>] []
  val _ = check ("auto without facts on subgoal 2 of 3: " ^ text NONE res)
    (is_some (#outcome res))
  (*auto proves subgoal 2, then tries the other subgoals in turn and stops at the first that it
    cannot prove*)
  val (_, res) = run "auto" 2 [\<^prop>\<open>Q 99\<close>, \<^prop>\<open>True\<close>, \<^prop>\<open>True\<close>] []
  val _ = check ("auto on subgoal 2 of 3: " ^ text NONE res)
    (is_none (#outcome res) andalso String.isSubstring "prefer 2 apply auto [1]" (text NONE res))
  (*the chained facts of the state stay*)
  val (_, res) = run' @{thms QR[OF PQ[OF P7]]} "simp" 2 [\<^prop>\<open>Q 99\<close>, \<^prop>\<open>R 7\<close>] []
  val _ = check ("subgoal 2 with a chained fact: " ^ text NONE res)
    (is_none (#outcome res) andalso String.isSubstring "prefer 2 apply simp" (text NONE res))

  val (_, res) = run "fast" 1 [\<^prop>\<open>R 7\<close>] [generated]
  val _ = check ("fast: " ^ text (preplay (Metis_Method (NONE, NONE, []))) res)
    (is_none (#outcome res) andalso
     text (preplay (Metis_Method (NONE, NONE, []))) res = text NONE res andalso
     String.isSubstring "by fast" (text NONE res))
  val (_, res) = run "simp" 1 [\<^prop>\<open>R 7\<close>] [generated]
  val _ = check ("simp with a preplay result: " ^ text (preplay Simp_Method) res)
    (String.isSubstring "simp add: QR[OF PQ[OF P7]]" (text (preplay Simp_Method) res))
  (*a preplay that failed or timed out does not replace the command that Try0 ran*)
  val _ = check ("simp with a failed preplay: " ^ text (preplay' Play_Failed Simp_Method) res)
    (text (preplay' Play_Failed Simp_Method) res = text NONE res andalso
     String.isSubstring "using QR[\"OF\" PQ [ OF P7 ]] by simp" (text NONE res))
  val _ = check "simp with a preplay that timed out"
    (text (preplay' (Play_Timed_Out (seconds 1.0)) Simp_Method) res = text NONE res)
end
\<close>

text \<open>The text for subgoal 2 is a proof.\<close>

lemma "True \<and> R 7"
  apply (rule conjI)
  prefer 2 using QR["OF" PQ [ OF P7 ]] apply simp
  apply simp
  done

subsection \<open>auto, fastforce and force take a global fact by using\<close>

ML \<open>
val _ =
  let
    val xref = Sledgehammer_Util.xref_of_name \<^context> "QR[OF PQ[OF P7]]"
    fun command name all_goals (facts : Try0.facts) =
      Try0_Util.apply_raw_named_method name all_goals Try0_Util.full_attrs
        Try0_HOL.silence_methods (SOME (seconds 10.0)) facts
        (Proof.theorem NONE (K I) [[(\<^prop>\<open>R 7\<close>, [])]] \<^context>)
      |> Option.map (clean o #command)
    val none = Try0.empty_facts
    fun directs name all_goals =
      command name all_goals
        {usings = [], directs = [xref], simps = [], intros = [], elims = [], dests = []}
  in
    [("auto", true), ("fastforce", false), ("force", false)]
    |> List.app (fn (name, all_goals) =>
      (check (name ^ ": " ^ the_default "NONE" (directs name all_goals))
        (directs name all_goals = SOME ("using QR[\"OF\" PQ [ OF P7 ]] by " ^ name));
       check (name ^ " with a simp rule")
        (command name all_goals
            {usings = [], directs = [], simps = [xref], intros = [], elims = [], dests = []} =
          SOME ("by (" ^ name ^ " simp: QR[\"OF\" PQ [ OF P7 ]])"))));
    check "no facts" (command "auto" true none = NONE)
  end
\<close>

subsection \<open>Try0, literal and dynamic facts, arguments of metis\<close>

ML \<open>
(*Try0 puts the facts of each kind where the method reads them*)
val _ =
  let
    fun command name config goal (facts : Try0.facts) =
      Try0_Util.apply_raw_named_method name false config Try0_HOL.silence_methods
        (SOME (seconds 10.0)) facts (Proof.theorem NONE (K I) [[(goal, [])]] \<^context>)
      |> Option.map (clean o #command)
    val xref = Sledgehammer_Util.xref_of_name \<^context>
    val none : Try0.facts = Try0.empty_facts
    val goal = \<^prop>\<open>P 7 \<Longrightarrow> Q 7\<close>
    open Try0_Util
  in
    check "Try0: a direct fact of blast"
      (command "blast" clas_attrs goal
          {usings = [], directs = [xref "PQ[of 7]"], simps = [], intros = [], elims = [], dests = []} =
        SOME "using PQ[\"of\" 7] by blast");
    check "Try0: a direct fact of argo"
      (command "argo" no_attrs \<^prop>\<open>R 7\<close>
          {usings = [], directs = [xref "QR[OF PQ[OF P7]]"], simps = [], intros = [], elims = [],
           dests = []} =
        SOME "using QR[\"OF\" PQ [ OF P7 ]] by argo");
    check "Try0: an introduction rule"
      (command "fastforce" full_attrs goal
          {usings = [], directs = [], simps = [], intros = [xref "PQ[of 7]"], elims = [], dests = []} =
        SOME "by (fastforce intro: PQ[\"of\" 7])");
    check "Try0: a destruction rule"
      (command "fastforce" full_attrs goal
          {usings = [], directs = [], simps = [], intros = [], elims = [], dests = [xref "PQ[of 7]"]} =
        SOME "by (fastforce dest: PQ[\"of\" 7])");
    check "Try0: an elimination rule"
      (command "fastforce" full_attrs goal
          {usings = [], directs = [], simps = [], intros = [], dests = [],
           elims = [xref "PQ[of 7, elim_format]"]} =
        SOME "by (fastforce elim: PQ[\"of\" 7, \"elim_format\"])");
    check "Try0: nothing to do" (command "fastforce" full_attrs \<^prop>\<open>Q 99\<close> none = NONE)
  end

(*a literal fact whose text is a plain string, as the tactic provers make it*)
val _ = check "the text of a literal fact"
  (Try0_Util.string_of_xref' \<^context> (Facts.Fact "P 7 \<Longrightarrow> Q 7", []) = "\<open>P 7 \<Longrightarrow> Q 7\<close>")

(*a dynamic fact*)
val _ =
  ["algebra_simps(2)", "algebra_simps(2-3)[symmetric]"]
  |> List.app (fn text =>
    check ("the facts of " ^ text ^ ": " ^ commas (map (fst o fst) (facts_of \<^context> text)))
      (forall (fn ((name, _), th) => evaluates_to \<^context> th name) (facts_of \<^context> text)))

(*arguments of metis that are no plain names*)
val _ =
  let
    fun names text =
      let val args = metis_args \<^context> text in
        maps (fn (ths, _) =>
          map (fn th => (Metis_Tactic.th_name_of_multi_thms \<^context> args th, th)) ths) args
      end
    fun named text expected =
      let val res = names text in
        check ("metis names of " ^ text ^ ": " ^ commas (map (the_default "NONE" o fst) res))
          (map fst res = map SOME expected andalso
           forall (fn (name, th) => evaluates_to \<^context> th (the name)) res)
      end
  in
    named "[[simp]]" ["[[simp]]"];
    named "\"four\"(2-3)" ["\"four\"(2)", "\"four\"(3)"];
    named "\"four\"(2-3)[simplified]" ["\"four\"(2)[simplified]", "\"four\"(3)[simplified]"]
  end
\<close>

text \<open>A tactic prover with a local fact that has no name.\<close>

notepad
begin
  fix k :: nat
  assume "P (length ''a  b'' + k)"
  ML_val \<open>
    local
      open Sledgehammer_Prover
      val ctxt = \<^context>
      val th = @{thm this}
      val goal = \<^prop>\<open>Q (length ''a  b'' + k)\<close>
      val state = Proof.theorem NONE (K I) [[(goal, [])]] ctxt
      val facts : Sledgehammer_Fact.fact list =
        [((Sledgehammer_Fact.cartouche_thm ctxt th,
            (ATP_Problem_Generate.Local, ATP_Problem_Generate.General)), th),
         (("PQ", stature), @{thm PQ})]
      val problem : prover_problem =
        {comment = "", state = state, goal = #goal (Proof.goal state), subgoal = 1,
         subgoal_count = 1, factss = [("mesh", facts)], has_already_found_something = K false,
         found_something = K (), memoize_fun_call = (fn f => f)}
      val params = Sledgehammer_Commands.default_params \<^theory> [("timeout", "30")]
      val res =
        Sledgehammer_Prover_Tactic.run_tactic_prover Normal "metis" params problem
          ((1, false, false, 2, "mesh"), No_Slice)
      val text = clean (#message res NONE)
    in
      val _ = check ("a tactic prover with an unnamed local fact: " ^ text)
        (is_none (#outcome res) andalso
         String.isSubstring "using \<open>P (length ''a  b'' + k)\<close> by (metis PQ)" text)
    end
  \<close>
  have "Q (length ''a  b'' + k)"
    using \<open>P (length ''a  b'' + k)\<close> by (metis PQ)
end

end
