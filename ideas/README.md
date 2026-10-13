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
- [state-trace-review.md](state-trace-review.md): the state-trace sketch read against the plan: what is new
  (nested loops without fragment lemmas, views instead of equations), where the sketch differs from what the plan
  expected and why, and the consequences for the plan.
- [deduction-engine-plan.md](deduction-engine-plan.md): the consolidated plan (revised Oct 13, 2026): the
  representation first, traces per strongly connected component of a loop's variables with views for the cycles,
  a sketch of combinators with several accumulators as first-class syntax, the steps S1 to S8 with their state,
  and the engine packages A to M with theirs.
- [deduction-engine-implementation.md](deduction-engine-implementation.md): the record of the implementation in
  the package `prove` (`-prove`, `-teq-state` over tuples) on the branch `prove`: the instructions, the decisions,
  the files, the state of each step and the log, to be picked up at any time.
- [state-trace.md](state-trace.md): the sketch of the representation question in the worktree `state-trace`:
  `-teq-state` with one state trace per loop over a datatype of the modified variables, whose per-variable traces
  are views that the matcher follows on demand, a fresh database, ten examples (the swap of two arrays, nested
  loops without fragment lemmas), the findings and a conclusion (Oct 12, 2026).
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
- [iterator-profiles.md](iterator-profiles.md): the loop patterns of LoopAnnotator (ASE 2026, iterator
  profiles) read against TEQs: what is covered (counters, conditional stores, sums, searches), what needs new
  lemmas (enumerations of set bits as in `for_each_cpu`, wrap-around, halving, reads of `a[i-1]` as chains),
  what is hard (lists, aliasing); benchmarks in `benchmarks/loopannotator`.
- [teq-lean.md](teq-lean.md): the open points of the Lean proofs of the database (implemented in `lean/`): the
  premises as `requires`, a Scala test of the generated statements, the legacy theorems, a Lean mode of the
  printer, faithful guards.
- [experiments.md](experiments.md): the plan of the experiments for a paper comparing TEQ with other
  techniques, with the reruns done and to do.

The findings behind the TEQ items are numbered in
[examples/dafny/algorithms/NOTES.md](../examples/dafny/algorithms/NOTES.md) and written up in
[doc/array-algorithms](../doc/array-algorithms); the observations on the code are in [TODO.md](../TODO.md).
