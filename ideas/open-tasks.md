# Open tasks by family (0.53.10)

The tasks of Arrays, Loops and MonoCera with the expected verdict true that 0.53.10 did not prove (cloud run of Oct 28,
2026), classified by their residual goals in the log files (`results/cuvee.all05310-*.logfiles.zip`), without runs.

| | Arrays | Loops |
|---|---|---|
| expected true, not proved | 128 | 329 |
| unknown, with a residual goal | 58 | 92 |
| timeout, no goal in the log | 44 | 191 |
| error | 26 | 46 |

MonoCera adds 14 unknown and 3 timeouts. The errors are the frontend (structs, the labels of the reducer variants,
field access, `__builtin_bswap32`), except 8 tasks with "rewriting does not terminate" (bugs.md).

The unknown tasks by the shape that the residual goal leaves unread:

| Family | Tasks | Left | Concept | Status |
|---|---|---|---|---|
| bAnd1-5, bor1-5 | 10 | `res = res & x[i]` as a raw trace | the aggregates `band`, `bor` with the folds `bands`, `bors` and the seed lemmas (aggregation.dfy) | done (Oct 28), examples/c/teq/bit_aggregates.c; `elems_selects_rotate` with a variable last position, unused before |
| sep05-1 ... sep60-2 | 5 | `sum(elems(maps(k :: F(x[k]))))` of a permuted array | the image of a multiset, `elems(maps(for xs yield v :: F(v))) == image(F, elems(xs))`, and maps reading an array at its keys as maps over `selects` | done (Oct 28) by parity: the guard of the remainder of C is one equation in both branches (Simplify.eq, Simplify.ite), the sum of 1 and -1 is `parity` (`sum_parity_indicator`), examples/c/teq/sep_parity.c; before, blocked: two sums that differ only in their bound variable are not equal (the same `sep` twice on one array stays unknown, engine-gaps.md "Not done"), and a higher-order variable whose argument has unbound variables, `F(a'[k])`, is not matched, which `image` would need for re-indexing too; no engine changes for now |
| array12/13/17/19/25/27-30_pattern, init-3-u | 10 | two-dimensional arrays, `a[r := a[r][k := v]]` | stores into one row as `stores` on the row, the rows as an in-place map | open |
| array2/3_pattern, mods, array10_pattern | 4 | `a[k := G(a[k], k)]` | an in-place map at distinct keys is `stores` with the values `G(a0[k], k)` | open |
| nr3, nr4, nr5 | 3 | `current(stores(b, maps(k' :: k' + 3 k), V))`, the inner loop folded | tiles: a read lemma for blocks of `m` cells | done (Oct 28): `select_current_tiles` (strides.dfy), nr3, nr4, nr5 correct locally (58, 46, 28 s), examples/c/teq/tiles.c; nr2 needs the keys `2 k + k'` (Scala) |
| loopv1, loopv3, bhmr2007 (C) | 3 | `sums` of 6 or 3, the goal `i % 3 == 0` | a sum of multiples of `m` is a multiple of `m` | loopv1 done (Oct 28): `sum_mod_multiples`, and `sum_above` with `0 < n \|\| e <= 0` by positive side conditions (Rewrite.holds), examples/c/teq/sum_multiples.c; loopv3 needs `m * (x / m)` as `x - x % m`, bhmr2007 a constant bound by a condition only (left) |
| partial_mod_count_2-5 | 4 | `counts` of `k % 2 == 0 && 500000 < k` | the count of the residues of a counter above a bound | open |
| geo2-ll, cohendiv-ll, cohencu-ll, prodbin-ll, mannadiv, ... | about 70 | nonlinear arithmetic, products modulo 2^64, `pow`, halving | series and arithmetic | mostly the solver's |
| array6/7_pattern | 2 | stencils that read cells written before | none | open |

The 235 timeouts are not classified, their logs have no goal.
