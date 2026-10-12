# Ideas

Proposals and experiments that are not implemented, consolidated on Oct 12, 2026; implemented proposals are
removed once their documentation lives in `doc/` (entry points, 0.42.0; the answers of `-verify`, 0.41.0, of
which only the open points remain).

- [teq-engine.md](teq-engine.md): the matcher, the simplifier and the diagnostics of `-teq -simplify`, the
  workarounds that every lemma written for a program carries, ordered by payoff (re-entrance guard, closed
  `invs` conditions matched, the pin in the matcher, ...), and cheap extensions of the method.
- [deduction-engine.md](deduction-engine.md): the findings of the hard algorithms read as symptoms of the matcher,
  the context and the strategy; a proposal for an engine without them (congruence closure, canonical forms and
  lookup, triggers and forward facts, equality saturation), and the representation question: state traces with
  the per-variable equations as projections.
- [deduction-engine-plan.md](deduction-engine-plan.md): the implementation plan for it, six phases with files,
  sizes, tests, what each retires, and a harness of four regression sets.
- [reentrance-guard.md](reentrance-guard.md): the plan for item 1 of teq-engine.md, a rule suspended while its own
  side conditions are evaluated, which cuts both cycles (the search through `invs` facts and the decision of a
  condition on the rule's own term).
- [teq-database.md](teq-database.md): what is ready to land (`nested` into `-teq`, the restated stores-ahead
  lemma, the chains), what is trusted without proof, lemma schemas and variadic patterns, the open shapes of the
  benchmarks.
- [binary-search.md](binary-search.md): the partial descriptions of traces on the binary search, verified with a
  cut; the lower bound of the algorithms as the open instance.
- [conditional-stores.md](conditional-stores.md): guarded stores merged into stores of conditional values, in
  `-teq` or the simplifier, instead of `2^s` cases.
- [trace-lemma-proofs.md](trace-lemma-proofs.md): deriving acceleration lemmas by fusion, induction in the tool
  for user lemmas; the proofs of the database are in Lean now.
- [verify-answers.md](verify-answers.md): the open points of `-verify`.
- [experiments.md](experiments.md): the plan of the experiments for a paper comparing TEQ with other
  techniques, with the reruns done and to do.

The findings behind the TEQ items are numbered in
[examples/dafny/algorithms/NOTES.md](../examples/dafny/algorithms/NOTES.md) and written up in
[doc/array-algorithms](../doc/array-algorithms); the observations on the code are in [TODO.md](../TODO.md).
