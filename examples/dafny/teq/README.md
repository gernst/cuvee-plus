# Trace equation systems

Examples of `-teq` (see [doc/teq.md](../../../doc/teq.md)) and its deduction engine `-prove` (see
[doc/prove.md](../../../doc/prove.md)): the variables of a loop are partitioned by the strongly connected components of
their read relation, each component is one trace (of several accumulators for a cycle), the per-variable traces of a
cycle are projections that `-prove` computes on demand, and the lemma database is
[resources/cuvee/teq.dfy](../../../resources/cuvee/teq.dfy). The first line of each file is its command line, the
`.out` file its expected output.

| example | loops | time (Oct 13, 2026) |
|---|---|---|
| counter, copy, init | single | 1.5 to 2 s |
| swap | single, two arrays that read each other ([swap.md](swap.md) has the proof) | 3 s |
| diamond | single, the loop diamond_1-1 of SV-COMP, by cases on a guard that does not change and on a remainder | |

These and the syntax example of traces with several accumulators,
[../parsing/traces_accumulators.dfy](../parsing/traces_accumulators.dfy), were in `examples/dafny/state` until Oct 23,
2026; the programs there that duplicated examples/dafny/algorithms replaced their versions in that folder.
