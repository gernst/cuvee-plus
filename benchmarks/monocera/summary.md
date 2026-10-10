# The benchmarks of MonoCera

The results are those of version 0.35.8 (October 10, 2026).

The CAV 2023 paper "Automatic Program Instrumentation for Automatic
Verification" (Amilon, Esen, Gurov, Lidström, Rümmer; technical report
arXiv 2306.00004, artifact doi:10.5281/zenodo.7875416) evaluates MonoCera,
TriCera with instrumentation for `\forall`, `\max`, `\min` and `\sum` over
arrays, on 125 tests derived from 109 SV-COMP programs of `array-*` and
`loop*` (one test per operator that the assertion admits) and 26 crafted
ones. The artifact's `run_tests` is in this directory. Each tool ran
on its own conversion of the programs (`polished_tests/<tool>`, produced by
`convert_cav23.py -nomalloc`, as the original logs in
`original_logs_from_paper` show): macros substituted, `malloc` replaced by
arrays, and for MonoCera the assertion replaced by an aggregate, often with
the loop that computes it commented out.

[convert_cuvee.py](convert_cuvee.py) converts the 125 SV-COMP tests in the
same way for Cuvée (`polished_tests/cuvee/<operator>`, with task definitions,
all expected true), keeping SV-COMP's harness and `__VERIFIER_assert`. The
run definition `MonoCera_unreach-call` of `xml/cuvee*.xml` in the root of the
repository takes them, one task set per operator. The runs used
[cuvee-quick.xml](../../xml/cuvee-quick.xml) and
[cuvee-quick-fallback.xml](../../xml/cuvee-quick-fallback.xml) (1 min,
2 cores, 7 GB); the paper's limits were 300 s wall time and 2700 s CPU time
on an AMD Opteron 2220 with 6 GB.

| Operator | tests | MonoCera | TriCera | CPAchecker | SeaHorn | Cuvée | Cuvée+Z3 |
|---|---|---|---|---|---|---|---|
| forall | 93 | 27 | 0 | 1 | 0 | 46 | 51 |
| max | 4 | 2 | 0 | 0 | 0 | 2 | 2 |
| min | 11 | 3 | 0 | 0 | 0 | 2 | 5 |
| sum | 17 | 10 | 0 | 0 | 0 | 1 | 1 |
| total | 125 | 42 | 0 | 1 | 0 | 51 | 59 |

- The columns of the paper's tools count the verified tests of the original
  logs; they agree with the paper (42 SV-COMP tests for MonoCera, 1 for
  CPAchecker). No wrong results; the spurious models of `-fallback`
  (`goal does not hold`, `Sat`) are `unknown`.
- 13 tests are proved by MonoCera and Cuvée (either configuration), 29 by
  MonoCera only (all `sum` tests of `array-fpi`, `brs1`-`brs5`, `ms1`-`ms5`,
  the `nr*`, `pr*`, `pnr*`, `rewnif*` of `array-tiling`,
  `max/sanfoundry_27_ground`, `min/rew`), 46 by Cuvée only (almost all
  `forall`: `eqn1`-`5`, `indp1`-`4`, `sina2`-`5`, `modn`, `modp`, `mods`,
  `array_init_pair_*`, `standard_init*`, `standard_copyInit*`). By programs:
  MonoCera 39, Cuvée 47, Cuvée+Z3 52.
- Without `-fallback`, unproved tests end within 10-45 s as `unknown` with
  open goals (69), 3 by timeout, 2 by `arrays of pointers are not
  supported` (`array_ptr_partial_init`, `partial_lesser_bound`). With
  `-fallback`, 25 tests of `forall` and 9 of `sum` reach the minute in z3,
  and `the length of a trace or list is unknown to -fallback` stops tests
  with nondeterministic input arrays, e.g. `sanfoundry_27_ground`.

The 69 `unknown` tests and a timeout leave 96 open goals, mostly one or two
per test. In 72 of them, the assertion of the checking loop survives as an
`invs` over its earlier iterations (printed as `all` up to version 0.35.10,
as in these logs): for `for (i=0; i<N; i++)
__VERIFIER_assert(b[i] == 2*i*i + 2*i + 1)` of `forall/ifeqn2`,

```
(invs ((k (butlast K)) (i (butlast I)))
  (= (select b k) (+ (* 2 k) (* 2 k k) 1)))
```

with `K == counter(0, 1, n)` the counter of the checking loop, and the goal
is the assertion at its current index `i == integer(n)`, `i < N`: an
induction step without a closed form of `b`, which is the `current` of the
trace of the loop that fills it, while the `invs` speaks about the checking
loop only. Elsewhere `invs` states the guards of the iterations of a loop
body, e.g. `(invs (... (tmp Tmp?)) (= tmp 0))` for a loop that did not
`break` before (`array_init_var_plus_ind`). Of the 96 goals, 64 have array
stores in a loop body, 57 a case split (`eps`), 41 `mod` or `div`, 40
nondeterministic input (`Tmp?`), 21 two or three loops, 10 aggregation
combinators (`sum`, `maxs`, `stores`, `selects`, `map`). The step that fails
is one of the following.

1. Recurrences on earlier entries, often with a polynomial closed form
   (`ifeqn1`-`5`, `ifcomp`, `pcomp`, `ifncomp`, `sqm`, `nsqm`, `condm`). In
   `ifeqn2`, `a[i] = a[i-1] + 4` and `b[i] = b[i-1] + a[i-1]`, and the goal
   is `b[i] == 2*i + 2*i*i + 1`; reading `b[i]` from the trace still refers
   to `b[i-1]` and `a[i-1]`, neither `a[k] == 4*k + 4` nor the closed form
   of `b` is derived.
2. Strided writes and parity (`mbpr*`, `pr*`, `pnr*`, partly `rew*`). In
   `pr2`, each iteration stores at `2*k` and `2*k + 1`, the bounds are
   `CELLCOUNT div 2` and `CELLCOUNT mod 2 == 0`. One goal has contradictory
   hypotheses (`1 < CELLCOUNT`, `CELLCOUNT mod 2 == 0`,
   `CELLCOUNT div 2 <= 0`), the other needs `volArray[i]` of the trace, by
   the parity of `i` and `k == i div 2`; membership appears as
   `occurs(k, map(... 2*k))`. In `pnr4` and `pnr5`, the cases of the
   nondeterministic values multiply (2^n cases of `eps`): the timeouts.
3. Sums accumulated in an array cell (all `sum` tests: `brs*`, `ms*`,
   `s*lif`, `conda`). In `brs2`, `sum[0] = sum[0] + a[i]` is a store at the
   constant index 0, which is not recognized as a sum over the trace, so
   that `sum[0] <= 2*N` with `a[k] <= 2` stays; the Dafny translations of
   `benchmarks/sv-comp` make `sum[0]` a scalar (see
   [its summary](../sv-comp/dafny/summary.md)), the C programs do not. In
   `conda`, `sum(selects(a, ...)) == 2*N` stays, over an array that a second
   loop modifies in place by its old contents.
4. Nondeterministic input arrays (40 goals: `standard_vararg_ground`,
   `sanfoundry_27_ground`, `array_init_pair_symmetr2`). In
   `standard_vararg_ground`, a `while` loop runs while `aa[a] >= 0`, and the
   checking loop asserts `aa[x] >= 0` for `x < a`: the `invs` of the first
   loop, `0 <= earlier(natural(k), Tmp?)`, has to be instantiated at the
   index `x` of the other; reads beyond the initialized prefix mix
   `earlier(..., Tmp?)` with `select(aa, k)`. Maxima need that each element
   is at most `maxs`.
5. Closed forms with division and nonlinear terms
   (`array_init_var_plus_ind*`). In `array_init_var_plus_ind`, the closed
   form `j == k*(k+1)/2` is found, and the goal is
   `0 <= (n + n*n) div 2` for `0 <= n`, which the simplifier does not decide
   (see the bounds of division under trace equation systems in
   [TODO.md](../../TODO.md)).
