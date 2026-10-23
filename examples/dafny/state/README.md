# Trace equation systems under -prove

Examples of `-teq -prove` (see [doc/teq.md](../../../doc/teq.md), [doc/prove.md](../../../doc/prove.md) and
[doc/prove.md](../../../doc/prove.md)): the variables of a loop are partitioned by
the strongly connected components of their read relation, each component is one trace (of several accumulators for a
cycle), the per-variable traces of a cycle are projections that the engine of `-prove` computes on demand, and the
lemma database is [resources/cuvee/teq.dfy](../../../resources/cuvee/teq.dfy). The
first line of each file is its command line, the `.out` file its expected output (no goal remains).

| example | loops | from | time (Oct 13, 2026) |
|---|---|---|---|
| counter, copy, init | single | examples/dafny/teq | 1.5 to 2 s |
| swap | single, two arrays that read each other | examples/dafny/teq ([swap.md](swap.md) has the proof) | 3 s |

`accumulators.dfy` shows the syntax of traces with several accumulators (`trace(e₁, e₂, for ... do x₁, x₂, k :: u₁, u₂)`,
`current(S).i`, `⌊S⌋.i`, see doc/teq.md), parsed, type-checked and printed.

The examples that duplicated programs of examples/dafny/algorithms with the database alone, the nested loops
(nested_counter, nested_sum, nested_mult, row_sums, transpose), lsearch and lower_bound, replaced the versions with
local lemmas there on Oct 23, 2026, as did the binary search `bsearch_bisect` (now
[examples/dafny/algorithms/bsearch.dfy](../algorithms/bsearch.dfy)); they run with the algorithms on demand
(`CUVEE_ALGORITHMS`). The variants of the binary search (`bsearch_safe`, `bsearch_sorted`, `bsearch`) were removed
on Oct 23, 2026 (see doc/prove.md).
