# Trace equation systems under -prove

Examples of `-teq -prove` (see [doc/teq.md](../../../doc/teq.md), [doc/prove.md](../../../doc/prove.md) and
[ideas/deduction-engine-plan.md](../../../ideas/deduction-engine-plan.md)): the variables of a loop are partitioned by
the strongly connected components of their read relation, each component is one trace (of several accumulators for a
cycle), the per-variable traces of a cycle are projections that the engine of `-prove` computes on demand, and the
lemma database is [resources/cuvee/teq.dfy](../../../resources/cuvee/teq.dfy). The
first line of each file is its command line, the `.out` file its expected output (no goal remains; the transpose
prints its summary lemma).

| example | loops | from | time (Oct 13, 2026) |
|---|---|---|---|
| counter, copy, init, lsearch | single | examples/dafny/teq | 1.5 to 2 s |
| swap | single, two arrays that read each other | examples/dafny/teq ([swap.md](swap.md) has the proof) | 3 s |
| nested_counter, nested_sum, nested_mult, row_sums | nested | examples/dafny/algorithms, without their lemmas | 2.5 to 9 s |
| transpose | nested, two-dimensional stores | examples/dafny/algorithms, one summary lemma on the nested fold | 5 s |

`accumulators.dfy` shows the syntax of traces with several accumulators (`trace(e₁, e₂, for ... do x₁, x₂, k :: u₁, u₂)`,
`current(S).i`, `⌊S⌋.i`, see doc/teq.md), parsed, type-checked and printed.

The binary searches, over a sorted array with the array, its bound and the key as parameters (`sorted(a, n)`):

| example | proof | time |
|---|---|---|
| bsearch_bisect | the version of doc/state-traces: the rule `bisection` names the trace of `lo` and `hi` with its probe and guards, two forward lemmas bound `lo` and `hi` by the cuts of the guards, which rules on sortedness rewrite to the partition points `lower(a, n, x)`, `upper(a, n, x)` | 8 s |
| bsearch_safe | the same with the probe `lo + (hi - lo) / 2`, which does not overflow | 10 s |
| lower_bound | the lower bound of examples/dafny/algorithms (open in the former per-variable form) with the same lemmas | 8 s |
| bsearch_sorted | in two layers: the monotonicity of each component as a forward invariant over its history first, so that the reads of the array within `a[0..n)` become comparisons with the partition points, then the bounds by the abstractions `incs`/`decs` | 45 s |
| bsearch | the search of examples/dafny/teq with constant partition points `p`, `q` in place of sortedness, the bounds of `incs`/`decs` as forward facts | 8 s |

The midpoint is bounded by the linear arithmetic (bounds of division by a constant). `bsearch_sorted` and `bsearch`
are kept as regression tests of the per-component route (see ideas/deduction-engine-implementation.md).
