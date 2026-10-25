# Ideas

Proposals, plans and open points that are not implemented; implemented proposals are removed once their
documentation lives in `doc/` (entry points, 0.42.0; the answers of `-verify`, 0.41.0, in
[doc/architecture.md](../doc/architecture.md); the deduction engine `-prove` and its design, in
[doc/prove.md](../doc/prove.md), Oct 14, 2026).

- [prove-next.md](prove-next.md): the open changes to the engine of `-prove`, ordered by expected gain, with what
  was tried: equalities from the simplex to the classes, the normal form of arithmetic atoms, naturals and integers
  (the rule statistics), remainders, the depth of case splits, rounds that do not settle, closed instances.
- [database-review.md](database-review.md): the review of the lemma database of Oct 23, 2026: usage on SV-COMP,
  what could be unified, the lemmas of examples/dafny/algorithms (copies, candidates, program-specific), the
  lemmas that work around gaps of the engine, the open points of earlier analyses.
- [conditional-stores.md](conditional-stores.md): guarded stores merged into stores of conditional values, in
  `-teq`, instead of `2^s` cases (the strided stores `pr3`-`pr5`).
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

The algorithms are described in [doc/algorithms.md](../doc/algorithms.md); their findings under the former
`-simplify` were numbered in the former examples/dafny/algorithms/NOTES.md (its history section) and written up in
[doc/array-algorithms](../doc/array-algorithms) (the state of Oct 11, 2026); the observations on the code are in
[TODO.md](../TODO.md), the bugs in [bugs.md](../bugs.md).
