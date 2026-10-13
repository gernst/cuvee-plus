# State traces

Examples of `-teq-state -prove` (see [doc/teq.md](../../../doc/teq.md), [doc/prove.md](../../../doc/prove.md) and
[ideas/deduction-engine-plan.md](../../../ideas/deduction-engine-plan.md)): the variables of a loop are partitioned by
the strongly connected components of their read relation, each component is one trace (of several accumulators for a
cycle), the per-variable traces of a cycle are projections that the engine of `-prove` computes on demand, and the
lemma database is the single module [resources/cuvee/teq/state.dfy](../../../resources/cuvee/teq/state.dfy). The
first line of each file is its command line, the `.out` file its expected output (no goal remains; the transpose
prints its summary lemma).

| example | loops | from | time (Oct 13, 2026) |
|---|---|---|---|
| counter, copy, init, lsearch | single | examples/dafny/teq | 1.5 to 2 s |
| swap | single, two arrays that read each other | examples/dafny/teq ([swap.md](swap.md) has the proof) | 3 s |
| nested_counter, nested_sum, nested_mult, row_sums | nested | examples/dafny/algorithms, without their lemmas | 2.5 to 9 s |
| transpose | nested, two-dimensional stores | examples/dafny/algorithms, one summary lemma on the nested fold | 22 s |

`accumulators.dfy` shows the syntax of traces with several accumulators (`trace(e₁, e₂, for ... do x₁, x₂, k :: u₁, u₂)`,
`current(S).i`, `⌊S⌋.i`, see doc/teq.md), parsed, type-checked and printed.

Kept as regression tests: `bsearch.dfy`, the binary search of examples/dafny/teq in the state form
with partition points in place of sortedness, which closes with the bounds of the `incs`/`decs` abstractions as
forward facts (`{:fw}`), see ideas/deduction-engine-implementation.md; the midpoint is bounded by the linear arithmetic.
`bsearch_sorted.dfy`, the same search over a sorted array with the array, its bound and the key as parameters (the
version of doc/state-traces): the reads of the array become comparisons with the partition points `lower(a, n, x)`,
`upper(a, n, x)` within `a[0..n)`, which needs `0 <= lo` and `hi <= n` in the update, from the monotonicity of each
component as forward invariants over its history (two layers, about 45 s).
`bsearch_bisect.dfy`, the same proved by a lemma over the whole cycle, a bisection whose guards hold on a prefix and
a suffix, which bounds `lo` and `hi` by the cuts of the guards, the partition points; 11 s.
`lower_bound.dfy`, the lower bound of the algorithms (open under `-teq -simplify`) with the same bisection lemmas; 8 s.
