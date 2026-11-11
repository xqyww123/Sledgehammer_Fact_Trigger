theory Readme_Example
  imports Main
begin

text \<open>The example of the README, as it stands there.\<close>

consts P :: "nat \<Rightarrow> bool" Q :: "nat \<Rightarrow> bool"

axiomatization where
  PQ [no_atp]: "P x \<Longrightarrow> Q x" and
  P7 [no_atp]: "P 7"

setup \<open>
  Context.theory_map (Sledgehammer_MePo.add_trigger "example"
    (fn {new_consts, ...} =>
      if member (op =) new_consts \<^const_name>\<open>Q\<close> then
        [{name = "PQ[OF P7]", prop = \<^prop>\<open>Q 7\<close>,
          stature = (ATP_Problem_Generate.Global, ATP_Problem_Generate.General)}]
      else []))
\<close>

ML \<open>
val goal = \<^prop>\<open>Q 7\<close>
val facts = Sledgehammer_Fact.nearly_all_facts_of_context \<^context> false
  Sledgehammer_Fact.no_fact_override [] [] goal
val res = Sledgehammer_MePo.mepo_suggested_facts \<^context>
  (Sledgehammer_Commands.default_params \<^theory> []) 64 NONE [] goal facts
val _ =
  if exists (fn ((name, _), _) => name = "PQ[OF P7]") res then ()
  else error "Failed check: the example of the README"
\<close>

end
