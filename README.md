# sledgehammer_fact_trigger

Sledgehammer selects the facts it gives to the provers from the theorems that are already stored.
This feature lets you register *fact triggers*: ML functions that generate further candidate facts
while Sledgehammer's relevance filter MePo runs. A generated fact is named by an Isar fact
expression such as `QR[OF PQ[OF P7]]`, so the proof that Sledgehammer prints can refer to it.

You need it when some facts are useful for proofs but are not worth storing in advance, because
there are too many of them and each is cheap to derive from stored theorems when it is needed.

This package changes Isabelle2026 only.

## Fact triggers

MePo works in rounds. In each round it accepts the facts that share enough constants with the goal
and with the facts accepted so far; the constants of the accepted facts then count as relevant in
the next round. A trigger is called once before the first round and once after every round:

```ML
Sledgehammer_MePo.add_trigger :
  string -> Sledgehammer_MePo.trigger -> Context.generic -> Context.generic

type trigger = trigger_input -> candidate list

type trigger_input =
  {ctxt       : Proof.context,
   hyp_ts     : term list,                 (* the premises of the goal *)
   concl_t    : term,                      (* the conclusion of the goal *)
   new_consts : string list,               (* the constants that became relevant in this round *)
   rel_consts : ptype list Symtab.table,   (* all relevant constants, with their type instances *)
   accepted   : lazy_fact list}            (* the facts accepted so far, most recent first *)

type candidate =
  {name    : string,     (* an Isar fact expression *)
   prop    : term,       (* its proposition, used to score the candidate *)
   stature : stature}
```

MePo scores a candidate like any other fact. It evaluates `name` only when it accepts the
candidate, and the expression must then denote exactly one theorem. `prop` is not compared with
that theorem. A trigger should return at once when `new_consts` holds nothing it cares about.

For example, this trigger offers `PQ[OF P7]` as soon as the constant `Q` becomes relevant:

```isabelle
setup \<open>
  Context.theory_map (Sledgehammer_MePo.add_trigger "example"
    (fn {new_consts, ...} =>
      if member (op =) new_consts \<^const_name>\<open>Q\<close> then
        [{name = "PQ[OF P7]", prop = \<^prop>\<open>Q 7\<close>,
          stature = (ATP_Problem_Generate.Global, ATP_Problem_Generate.General)}]
      else []))
\<close>
```

Triggers do not run when Sledgehammer is given `fact_filter = mash`, or only the facts listed in
its invocation, because MePo does not run then.

## Other changes

- Sledgehammer's tactic provers (`metis`, `simp`, `auto`, ...) accept fact names that carry
  attributes. Before, only a plain name or a name with one selection such as `foo(2)` worked.
- `try0` prints a fact with nested attributes, such as `QR[OF PQ[OF P7]]`, and a fact whose name
  needs quotes, such as `"1.IH"(2)`, as text that Isar parses.

## Sources

The Isabelle sources a version of this package was made from, with this feature and the ones it is
built on, are a tag of [isabelle-patched](https://github.com/xqyww123/isabelle-patched) named
`<Isabelle release>/sledgehammer_fact_trigger/<m>`, where `<m>` is the last number of the package's
version: version `2026.0.1` was made from `Isabelle2026/sledgehammer_fact_trigger/1`.
