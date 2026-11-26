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
the next round. A trigger is called before every round:

```ML
Sledgehammer_MePo.add_trigger :
  string -> Sledgehammer_MePo.trigger -> Context.generic -> Context.generic

type trigger = trigger_input -> candidate list

type trigger_input =
  {ctxt       : Proof.context,
   hyp_ts     : term list,                 (* the premises of the goal *)
   concl_t    : term,                      (* the conclusion of the goal *)
   new_consts : string list,               (* the names whose entry in rel_consts changed in the
                                              last round, or all of them before the first round *)
   rel_consts : ptype list Symtab.table,   (* all relevant constants, with their type instances *)
   accepted   : Sledgehammer_Fact.lazy_fact list}   (* the facts accepted, most recent first *)

type candidate =
  {name    : unit -> string,   (* the Isar fact expression written into a proof *)
   thm     : thm lazy,         (* the fact itself *)
   prop    : term,             (* its proposition, used to score the candidate *)
   stature : stature}
```

Besides constants, these names include free variables and MePo's pseudo-constants, and a name
appears again whenever it gains a new type instance. `Sledgehammer_MePo.typargs_of_ptype` gives the
type arguments of each type instance in an entry of `rel_consts`.

`hyp_ts` and `concl_t` are what the caller of MePo passes. They need not be closed terms: they may
contain free variables that are not fixed in `ctxt`, and a caller other than Sledgehammer may pass
terms with loose bound variables, whose types these terms do not record. Inside any term, a subterm
under a binder contains loose bound variables. A trigger that needs the type of such a subterm
should carry the types of the binders above it, as `fastype_of1` does, or open the binders with
`Term.dest_abs_fresh`; `fastype_of` raises `TERM` on a loose bound variable.

MePo scores a candidate like a fact of the current theory. Candidates whose `prop` is the same up
to renaming of schematic variables count once. MePo calls each trigger before its first round, with
all constants of the goal in `new_consts`, and after each round, with the constants that became
relevant in that round. Candidates from the call before the first round take part in the first
round; candidates from the call after round k take part from round k + 1 on, so they rank behind
the facts accepted up to round k, which can include facts of the pool that contain the same
constants. A trigger that fires on constants of the goal thus gives its candidates the best chance.
The `stature` of a candidate counts in its score as for any fact: `Simp`, `Intro` and `Elim` get a
bonus. MePo forces `thm` and calls `name` only for a candidate that it accepts, so a candidate
that is rejected costs neither. `name` must give one
fact reference as Isar reads it (for example a name with an optional selection and optional
attributes), not several references in a row, and that reference must denote `thm` where the proof
is replayed: MePo does not evaluate the text, so this is up to the trigger. `prop` is not compared
with `thm`. A trigger should return at once when `new_consts` holds nothing it cares about.

A trigger must be a pure function: MePo runs in parallel with MaSh. An exception raised by a
trigger, or by forcing the `thm` of a candidate that MePo accepts, stops Sledgehammer with that
exception. Where Isabelle itself goes on after an error of Sledgehammer, it also goes on after this
one: the `try` command and automatic Sledgehammer show nothing, and Mirabelle writes the error to
its log.

Triggers are registered by name: registering a trigger under a name that is in use replaces the
earlier one. Every caller of MePo runs the triggers, not only the `sledgehammer` command.

For example, this trigger offers `PQ[OF P7]` as soon as the constant `Q` becomes relevant:

```isabelle
setup \<open>
  Context.theory_map (Sledgehammer_MePo.add_trigger "example"
    (fn {new_consts, ...} =>
      if member (op =) new_consts \<^const_name>\<open>Q\<close> then
        [{name = K "PQ[OF P7]", thm = Lazy.value @{thm PQ[OF P7]}, prop = \<^prop>\<open>Q 7\<close>,
          stature = (ATP_Problem_Generate.Global, ATP_Problem_Generate.General)}]
      else []))
\<close>
```

Triggers do not run when Sledgehammer is given `fact_filter = mash`, or only the facts listed in
its invocation, because MePo does not run then.

## Other changes

A generated fact is named by an Isar fact expression, so this package also corrects how
Sledgehammer, Try0 and Metis write fact references into proof text, and how Sledgehammer's tactic
provers (`metis`, `simp`, `auto`, ...) use them. In this list, "before" means Isabelle2026 without
this package.

- The tactic provers accept fact names that carry attributes. Before, only a plain name or a name
  with one selection such as `foo(2)` worked. `auto`, `fastforce` and `force` take global facts by
  `using`, as in `using foo by auto`; before, these three gave up whenever they were given a
  global fact. Sledgehammer can therefore report more proofs by these methods. It starts no further
  prover attempt once it has found `max_proofs` proofs (4 by default), so it can report fewer
  proofs by external provers than before.
- A tactic prover works on the subgoal that Sledgehammer was asked about; when that is not the
  first subgoal, its proof text selects it with `prefer n`. Before, it always worked on the first
  subgoal and could report a proof of the wrong subgoal. As before, `auto` goes on with the next
  subgoals once it has proved one, as in `apply auto [2]`; after `prefer n`, these include the
  subgoals that came before subgoal n.
- A tactic prover shows the command that it ran. With `instantiate`, the one-line proof with
  instantiated facts is shown instead only if it was replayed with success.
- A fact reference is printed as text that Isar reads back as the same fact: nested attributes as
  in `QR[OF PQ[OF P7]]`, several attributes in one list, names that need quotes such as
  `"1.IH"(2)`, anonymous facts `[[...]]`, and literal facts.
- For the facts given as `sledgehammer (foo bar)`, each theorem has a name of its own, such as
  `foo(2)[of x]`, in the order in which the reference yields the theorems. Each theorem is what
  its name denotes on its own.
- The name of a local fact without a name is its proposition; blanks inside a string of that
  proposition are kept, and so are those in the predicate of an instantiated induction rule
  (`nat.induct[where P = "..."]`).
- When the name of a fact that a proof uses cannot be read back, the proof that an external prover
  found is still shown. Before, it was lost.
- Metis writes `of` instantiations for an anonymous fact inside its brackets, and names a local
  fact `a` instead of `??.local.a`.

Known limits:

- A name that is a printed proposition may still not be read back as that proposition. For example,
  the local facts `(0::int) ≤ 1` and `(0::nat) ≤ 1` both get the name `‹0 ≤ 1›`, and Isar rejects
  that name as ambiguous. A tactic prover that is given a fact with such a name gives up.
- A fact of several theorems with attributes that both declare into the context and depend on it,
  such as `foo[simplified, simp]`: Isar reads the names of one proof in order, so a later name can
  denote a theorem that differs from the one a prover was given for it. For an argument of this
  kind in a `metis` call, the names that Metis itself prints for the theorems after the first can
  be wrong.
- The statements in the Isar proofs that Sledgehammer prints are not changed by this package:
  blanks inside a string are still collapsed, and the type annotations that Sledgehammer puts on
  constants are still lost (`(1::int) + 2 = 3` is printed as `1 + 2 = 3`), so a statement may not be
  read back as the proposition that was proved.

New in version 2026.0.4: `auto`, `fastforce` and `force` with global facts; the subgoal of a tactic
prover; the command that a tactic prover shows; the theorems of a fact given as `sledgehammer (foo)`
are evaluated one by one; blanks in the names of unnamed facts and in instantiated induction rules;
proofs of external provers are no longer lost; `of` instantiations of anonymous facts; a
trigger's candidate carries its theorem (`thm`) and makes its name on demand (`name`), and MePo no
longer evaluates the text of the name (an incompatible change of the type `candidate`).

## Sources

The Isabelle sources a version of this package was made from, with this feature and the ones it is
built on, are a tag of [isabelle-patched](https://github.com/xqyww123/isabelle-patched) named
`<Isabelle release>/sledgehammer_fact_trigger/<m>`, where `<m>` is the last number of the package's
version: version `2026.0.1` was made from `Isabelle2026/sledgehammer_fact_trigger/1`.
