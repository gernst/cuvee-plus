# Open tasks by family (0.53.10)

The tasks of Arrays, Loops and MonoCera with the expected verdict true that 0.53.10 did not prove (cloud run of Oct 28,
2026), classified by their residual goals in the log files (`results/cuvee.all05310-*.logfiles.zip`), without runs.
The families done since are documented in doc/teq.md (bAnd, bor, sep, nr3-nr5, loopv1 and rewnifrev in 0.53.14).

| | Arrays | Loops |
|---|---|---|
| expected true, not proved | 128 | 329 |
| unknown, with a residual goal | 58 | 92 |
| timeout, no goal in the log | 44 | 191 |
| error | 26 | 46 |

MonoCera adds 14 unknown and 3 timeouts. The errors are the frontend (structs, the labels of the reducer variants,
field access, `__builtin_bswap32`), except 8 tasks with "rewriting does not terminate" (bugs.md).

The open families by the shape that the residual goal leaves unread:

| Family | Tasks | Left | What it needs |
|---|---|---|---|
| array12/13/17/19/25/27-30_pattern, init-3-u | 10 | two-dimensional arrays, `a[r := a[r][k := v]]` | a fold for the stores into one row, then the rows as an in-place map |
| nr2 | 1 | the inner loop of two iterations keeps the cases `c[2k := j]`, `c[2k + 1 := 0]`, whose indices the canonical forms write with the literal of `k'` | the shared key `2k + k'` synthesized from the cases (Rewrite.update), then `select_current_tiles` |
| loopv3 | 1 | `4 * (i / 4) == i` for a sum of 8 or 4 | `m * (x / m)` as `x - x % m` in the arithmetic, then `sum_mod_multiples` (set aside: no divisibility constraints for now) |
| bhmr2007 (C) | 1 | `a + b == 3 * n` for two sums whose values add up to 3 | a lemma whose constant is bound by its side condition only, which rules do not allow |
| partial_mod_count_2-5 | 4 | `counts` of `k % 2 == 0 && 500000 < k` | the count of the residues of a counter above a bound (arithmetic, set aside) |
| mods | 1 | an in-place map over a counter by the sign of the read, then `(N + 1) % (N + 1)` | `stores_cases` with a function in both cases, and the remainder by a symbolic modulus (arithmetic) |
| array2/3/10_pattern | 3 | stores at nondeterministic, repeating keys; the cancellation of two arrays; nonlinear goals | none in the database (ideas/README.md: array-patterns set aside) |
| array6/7_pattern | 2 | stencils that read cells written before | none |
| geo2-ll, cohendiv-ll, cohencu-ll, prodbin-ll, mannadiv, ... | about 70 | nonlinear arithmetic, products modulo 2^64, `pow`, halving | series and arithmetic, mostly the solver's |

The 235 timeouts are not classified, their logs have no goal.
