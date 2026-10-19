# Ideas

Proposals, plans and open points that are not implemented; implemented proposals are removed once their
documentation lives in `doc/` (entry points, 0.42.0; the answers of `-verify`, 0.41.0, in
[doc/architecture.md](../doc/architecture.md); the deduction engine `-prove` and its design, in
[doc/prove.md](../doc/prove.md), Oct 14, 2026).

- [work-queue.md](work-queue.md): the open items of the current work on the database and the engine, by expected
  gain.
- [prove-next.md](prove-next.md): the planned changes to the engine of `-prove` after the database migration, with
  what was tried.
- [conditional-stores.md](conditional-stores.md): guarded stores merged into stores of conditional values, in
  `-teq`, instead of `2^s` cases (the strided stores `pr3`-`pr5`).
- [iterator-profiles.md](iterator-profiles.md): the loop patterns of LoopAnnotator (ASE 2026, iterator
  profiles) read against TEQs: what is covered (counters, conditional stores, sums, searches), what needs new
  lemmas (enumerations of set bits as in `for_each_cpu`, wrap-around, halving, reads of `a[i-1]` as chains),
  what is hard (lists, aliasing); benchmarks in `benchmarks/loopannotator`.
- [witnesses.md](witnesses.md): verification witnesses for SV-COMP: the formats of C and SV-LIB, why TEQ
  proofs contain no invariants and how to extract them, the missing quantifiers of C witnesses, and a plan from
  trivial witnesses over the invariants of `-chc` to quantified invariants for arrays; the source positions
  through the scanner, the grammar and the C parser into the attributes of loops.
- [ltl.md](ltl.md): linear temporal specifications by weakest preconditions (ISoLA 2026): temporal
  `guarantees` of Dafny methods and loops with hypothesis operators, a forward generator in `-vcgen`, the
  lowering of the goals for solvers, and points of the paper to check.
- [experiments.md](experiments.md): the plan of the experiments for a paper comparing TEQ with other
  techniques, with the reruns done and to do.

The findings of the algorithms under the former `-simplify` are numbered in
[examples/dafny/algorithms/NOTES.md](../examples/dafny/algorithms/NOTES.md) and written up in
[doc/array-algorithms](../doc/array-algorithms) (the state of Oct 11, 2026); the observations on the code are in
[TODO.md](../TODO.md), the bugs in [bugs.md](../bugs.md).
