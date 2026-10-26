# Ideas

Proposals, plans and open points that are not implemented; a proposal is removed once it is implemented and
documented in `doc/`.

- [portfolio.md](portfolio.md): a wrapper (portfolio.py) that runs fuzzing, cuvee-fallback, `-chc` and bounded
  unrolling in parallel on the native binary, with what each method is good at and the steps.
- [slice.md](slice.md): whether `-slice` proves tasks on its own (three quarters of what `-teq` proves), why it cannot
  answer without a goal, the program as the unit of answer, `incorrect` and the fallback inside `-slice`.
- [prove-next.md](prove-next.md): the plan (the regressions since 0.51.4, bounded unrolling for counterexamples and
  bounded proofs) and the open changes to the engine of `-prove`, ordered by expected gain.
- [canonical.md](canonical.md): the open points of the canonical forms of the context and of the integer counts.
- [database-review.md](database-review.md): the lemma database: what could be unified, candidates among the lemmas
  of examples/dafny/algorithms, the lemmas that work around gaps of the engine.
- [array-lemmas.md](array-lemmas.md): the open classes of SV-COMP Arrays (Oct 26, 2026), the lemmas added to the
  database, the workarounds in [array-lemmas.dfy](array-lemmas.dfy) with the gaps of the engine they wait for, the
  plan for reducer commutativity.
- [dnf-guards.md](dnf-guards.md): the cases of updates with conjunctive guards (DNF) instead of cases merged by
  equal results, the merging moved into the matcher for higher-order guard variables.
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

The algorithms are described in [doc/algorithms.md](../doc/algorithms.md); the observations on the code are in
[TODO.md](../TODO.md), the bugs in [bugs.md](../bugs.md).
