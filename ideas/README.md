# Ideas

Proposals, plans and open points that are not implemented; a proposal is removed once it is implemented and
documented in `doc/`.

The open work and its order are the work queue of [TODO.md](../TODO.md); this directory holds the plans and the
analyses behind its items. Files marked as history record what was tried and not taken.

- [open-tasks.md](open-tasks.md): the open tasks of 0.53.10 with the expected verdict true by family, with the concept
  each needs.

- [portfolio.md](portfolio.md): a wrapper (portfolio.py) that runs fuzzing, cuvee-fallback, `-chc` and bounded
  unrolling in parallel on the native binary, with what each method is good at and the steps.
- [slice.md](slice.md): whether `-slice` proves tasks on its own (three quarters of what `-teq` proves), why it cannot
  answer without a goal, the program as the unit of answer, `incorrect` and the fallback inside `-slice`.
- [prove-next.md](prove-next.md): the plan (the regressions since 0.51.4, bounded unrolling for counterexamples and
  bounded proofs) and the open changes to the engine of `-prove`, ordered by expected gain.
- [canonical.md](canonical.md): the open points of the canonical forms of the context and of the integer counts.
- [database.md](database.md): the lemma database: the raw traces and their named folds, overlaps among the lemmas,
  what could be unified, the workarounds for gaps of the engine, the candidates among the lemmas of the algorithms,
  and the decisions (removed, kept, rejected, not taken).
- [engine-gaps.md](engine-gaps.md): a plan to close the gaps of `-prove` behind the workarounds of the database
  (comparisons of conditionals, `-debug match`, iteration variables kept instead of literals, remainders and division,
  higher-order values at arithmetic arguments), the database work, and what is not done and why.
- [engine-consolidation.md](engine-consolidation.md): a review of the engine of `-prove`: the places that decide
  normal forms, equality, derived facts, alternatives in matching, memos and choices, with proposals to unify them.
- [dnf-guards.md](dnf-guards.md): the cases of updates with conjunctive guards (DNF) instead of cases merged by
  equal results, the merging moved into the matcher for higher-order guard variables.
- [conditional-stores.md](conditional-stores.md) (history): guarded stores merged into stores of conditional values, in
  `-teq`, instead of `2^s` cases (the strided stores `pr3`-`pr5`).
- [cases-and-folds.md](cases-and-folds.md): the plan after 0.53.1: cases instead of if-then-else in `maps` and at
  the reads of maps with cases, keys without values per case, the overlaps among the lemmas, and the raw traces of
  the database that could become named folds.
- [iterator-profiles.md](iterator-profiles.md): the loop patterns of LoopAnnotator (ASE 2026, iterator
  profiles) read against TEQs: what is covered (counters, conditional stores, sums, searches), what needs new
  lemmas (enumerations of set bits as in `for_each_cpu`, wrap-around, halving, reads of `a[i-1]` as chains),
  what is hard (lists, aliasing); benchmarks in `benchmarks/loopannotator`.
- [witnesses.md](witnesses.md): verification witnesses for SV-COMP: the formats of C and SV-LIB, why TEQ
  proofs contain no invariants and how to extract them, the missing quantifiers of C witnesses, and a plan from
  trivial witnesses over the invariants of `-chc` to quantified invariants for arrays; inductive invariants for
  SV-LIB from the TEQ system without the goal (simplified, potentially lowered); the source positions
  through the scanner, the grammar and the C parser into the attributes of loops.
- [ltl.md](ltl.md): linear temporal specifications by weakest preconditions (ISoLA 2026): temporal
  `guarantees` of Dafny methods and loops with hypothesis operators, a forward generator in `-vcgen`, the
  lowering of the goals for solvers, and points of the paper to check.
- [implement.md](implement.md): the open points of the implementations of
  [doc/implement.md](../doc/implement.md): shared abstract functions, refinement obligations as goals.
- [renc-verification.md](renc-verification.md): verifying the encoding of renc with `-vcgen` and cvc5: contracts
  over the abstract types, coupling invariants, the intended meaning of the predicates along the run with true
  answers, the global conditions checked separately, and the gaps of the current setup.
- [nondet.md](nondet.md): determinization of every source of nondeterminism (havoc, uninitialized variables, choice,
  iteration, calls by contract, ODEs) by an oracle `nondet(ticks)` with a global counter, for witnesses, `-teq`, and
  nondeterministic implementations as expressions.
- [experiments.md](experiments.md): the plan of the experiments for a paper comparing TEQ with other
  techniques, with the reruns done and to do.

The algorithms are described in [doc/algorithms.md](../doc/algorithms.md); the observations on the code are in
[TODO.md](../TODO.md), the bugs in [bugs.md](../bugs.md).
