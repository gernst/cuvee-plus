# Trace equation systems under -prove

Examples of `-teq -prove` (see [doc/teq.md](../../../doc/teq.md), [doc/prove.md](../../../doc/prove.md) and
[doc/prove.md](../../../doc/prove.md)): the variables of a loop are partitioned by
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

The binary search over a sorted array, proved by the rule `bisection` over the whole cycle, is
[examples/dafny/algorithms/bsearch.dfy](../algorithms/bsearch.dfy) (formerly `bsearch_bisect` here), which runs with
the algorithms on demand (`CUVEE_ALGORITHMS`); its variants (`bsearch_safe`, `bsearch_sorted`, `bsearch`) were
removed on Oct 23, 2026 (see doc/prove.md).

| example | proof | time |
|---|---|---|
| lower_bound | the lower bound of examples/dafny/algorithms (open in the former per-variable form) with the lemmas of the bisection | 8 s |
