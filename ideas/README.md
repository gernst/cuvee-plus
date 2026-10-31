# Ideas

Proposals, plans and open points that are not implemented; a proposal is removed once it is implemented and
documented in `doc/`.

The open work and its order are the work queue of [TODO.md](../TODO.md); this directory holds the plans and the
analyses behind its items. Files marked as history record what was tried and not taken.

- [engine.md](engine.md): the engine of `-prove`: the context and its canonical forms, the arithmetic (forward
  instances in the final check, exact and symbolic division), decisions and derived facts, matching, choices and
  guards in DNF, search and speed (rounds that do not settle, bounded unrolling), the open tasks of nla-digbench by
  concept (preserved invariants, doubling, guarded increments, binary expansion), what is not done and why, the
  design notes and the history of the regressions.
- [database.md](database.md): the lemma database: the raw traces and their named folds, overlaps among the lemmas,
  what could be unified, the workarounds for gaps of the engine, cases and choices, the conditional stores (history),
  the candidates among the lemmas of the algorithms, and the decisions (removed, kept, rejected, not taken).
- [residual-goals.md](residual-goals.md): the residual goals of the unknown tasks of 0.53.22 by principle: induction
  with the iteration constraint as hypothesis, the constraint at the last iteration, reads of constant arrays,
  arguments modulo the context, ties of max and min, missing lemmas, residue counts under wrap-around, arithmetic.
- [open-tasks.md](open-tasks.md): the open tasks of 0.53.22 (cloud, 300 s) with the expected verdict true by family,
  with what each still needs.

- [slice.md](slice.md): whether `-slice` proves tasks on its own (three quarters of what `-teq` proves), why it cannot
  answer without a goal, the program as the unit of answer, `incorrect` and the fallback inside `-slice`.
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
The algorithms are described in [doc/algorithms.md](../doc/algorithms.md); the observations on the code are in
[TODO.md](../TODO.md), the bugs in [bugs.md](../bugs.md).
