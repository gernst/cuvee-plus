# State traces

Examples of `-teq-state -prove` (see [doc/teq.md](../../../doc/teq.md), [doc/prove.md](../../../doc/prove.md) and
[ideas/state-trace.md](../../../ideas/state-trace.md)): each loop with several modified variables is summarized by
one trace over the tuple of them, the per-variable traces are views that the engine of `-prove` follows on demand, and
the lemma database is the single module [resources/cuvee/teq/state.dfy](../../../resources/cuvee/teq/state.dfy). The
first line of each file is its command line, the `.out` file its expected output (no goal remains; the transpose
prints its summary lemma).

| example | loops | from | time (Oct 13, 2026) |
|---|---|---|---|
| counter, copy, init, lsearch | single | examples/dafny/teq | 1.5 to 2 s |
| swap | single, two arrays that read each other | examples/dafny/teq ([swap.md](swap.md) has the proof) | 3 s |
| nested_counter, nested_sum, nested_mult, row_sums | nested | examples/dafny/algorithms, without their lemmas | 2.5 to 9 s |
| transpose | nested, two-dimensional stores | examples/dafny/algorithms, one summary lemma on the nested fold | 22 s |
