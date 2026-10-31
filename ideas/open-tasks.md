# Open tasks by family (0.53.22, Oct 30)

The tasks of Arrays and Loops with the expected verdict true that the cloud run `all05322x5` did not prove (0.53.22
with the memo of solutions, released as 0.53.23; `-svcomp -rules`, 300 s, one core, Xeon E3-1230 v5; Arrays 271 true
proved, Loops 254), classified by their status and residual goals; MonoCera from `all05319r` (0.53.19, 120 s, Ryzen).
The engine's side of each gap is in [engine.md](engine.md), the database's in [database.md](database.md).

| | Arrays | Loops |
|---|---|---|
| expected true, not proved | 111 | 301 |
| unknown, with a residual goal | 58 | 105 |
| timeout | 25 | 149 |
| error of the frontend | 19 | 44 |
| "rewriting does not terminate" | 8 | 3 |
| other errors | 1 (relax-2-2, an unknown function) | |

Of Loops, 197 are nla-digbench (16) and nla-digbench-scaling (181), by concept in engine.md, section 7. MonoCera: forall
81 of 93, max 4 of 4, min 9 of 11, sum 17 of 17.

The errors of the frontend: `goto` to a label whose statement falls through (26, the reducer variants), parse errors
(32: structs, the reducer variants of loop-lit and loop-invgen, aiob and ofuf of loop-industry-pattern,
array-lopstr16), arrays of pointers (2), indexing of a variable that is not an array (duplets, prefixsum_iter), not an
integer (veris NetBSD). Non-termination: reducercommutativity max05-1 to max60-2, diff-2-n-u, copy-partial-3-u,
partial_mod_count_limited_gen, fermat1-ll_valuebound1, 2, 10 (bugs.md).

## Arrays

| Family | Tasks | Left | What it needs |
|---|---|---|---|
| array-patterns | 30 | stores at nondeterministic, repeating keys into two arrays, a final sum bounded by a closed form; 4 time out | the sums of two arrays related pointwise; none in the database (TODO.md) |
| array-multidimensional | 12 | two-dimensional arrays `a[r := a[r][k := v]]` (copy-3-n-u, init-3-u, init-non-constant-3-u, transpose-u unknown; add, diff, init-4, max, min, rev time out) | a fold for the stores into one row, then the rows as an in-place map |
| partial_mod_count_2-5, _limited_* | 10 | `counts` of `k % 2 == 0 && 500000 < k`; conditional stores whose second value is not a constant | the count of the residues of a counter above a bound (`count_remainder_offset` and `_positive`, uncommitted, give the residues from 0) |
| array-examples | 8 | sanfoundry_02, 10, 43 (arrays are values, bugs.md), sorting_bubblesort, selectionsort, standard_vararg (an iteration constraint read at a witness), the set_multi_proc pair (time out) | per task |
| array-crafted | 9 | xor1-5 (no aggregate for xor), bAnd5, bor5 (a variable `N`), mapsum5, mapavg5 | xor as an aggregate over multisets; the variable size |
| array-tiling | 7 | nr2 (cases `c[2k := j]`, `c[2k + 1 := 0]` with the literal of `k'`), mbpr4 (the case `i == 2` of `0 < i < 3`), mbpr5, rewrev, skipped; pnr4, pnr5 time out | engine.md 4.2 and 5.3 |
| reducercommutativity | 2 | max (unknown), sep (time out at 300 s; correct locally in 0.53.14) | max as an aggregate; max05-1 to max60-2 do not terminate (bugs.md) |
| array-cav19 | 4 | array_init_nondet_vars, array_init_pair_symmetr2 (the constraint not instantiated at the read), array_init_both_ends_multiple_sum, array_min_and_copy_shift_sum_add | rules on the atoms of the goals (engine.md, section 8) |
| array-fpi | 1 | mods: an in-place map by the sign of the read, then `(N + 1) % (N + 1)` | `stores_cases` with a function in both cases, a remainder by a symbolic modulus |

## Loops (without nla-digbench)

| Family | Tasks | Left | What it needs |
|---|---|---|---|
| loops-crafted-1 | 14 | sumt2-sumt9 (terms with binders not compared modulo bound names; sumt7-9 time out), loopv3 (`4 * (i / 4) == i`), iftelse (correct locally with the uncommitted residue counts), mono-crafted_13, theatreSquare, nested5-1 and nested_delay_nd (time out) | sumt: engine.md, section 8; loopv3: `m * (x / m)` as `x - x % m`, set aside |
| loop-lit | 10 | bhmr2007 (`a + b == 3 * n`, a constant bound by a side condition only), as2013-hybrid, bh2017-ex3, ddlm2013, gj2007b, gr2006, gsv2008, hh2012-ex2b, mine2017-ex4.7; bh2017-ex-add times out | engine.md 4.3; the others are not classified |
| loops | 9 | array-1, eureka_05, insertion_sort-2-2, nec40, trex01-2, trex03-2 unknown; eureka_01-2, matrix-1, vogal-1 time out | not classified |
| loop-invgen | 7 | apache-escape-absolute, half_2, nest-if3, nested6, sendmail-close-angle unknown; apache-get-tag, heapsort time out | not classified |
| loop-invariants(64) | 6 | bin-suffix-5, const, eq1, linear-inequality-inv-a, c, d | invariants without closed forms (as A1 of engine.md, section 7) |
| loop-new | 3 | count_by_k (rounding, cancellation of factors), count_by_nondet, nested-1 (the composition `k == n * m`) | engine.md 2.4 |
| loop-acceleration | 3 | phases_2-2, underapprox_1-2; diamond_2-2 times out (2^10 paths) | |
| verifythis | 2 | elimination_max, lcp | |
| loop-zilu, loop-simple, loop-crafted | 5 | benchmark32_linear, benchmark52_polynomial; nested_5, nested_6 time out; simple_array_index_value_4 | |
| loop-industry-pattern | 1 | mod3 | |

The rows count the tasks without errors. The timeouts have no goal in their logs and are classified by their
programs only.
