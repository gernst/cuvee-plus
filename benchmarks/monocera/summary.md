# The benchmarks of MonoCera

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

## Setup

- **Cuvée**: [convert_cuvee.py](convert_cuvee.py) converts the 125 SV-COMP
  tests in the same way (`polished_tests/cuvee/<operator>`, with task
  definitions, all expected true), keeping SV-COMP's harness and
  `__VERIFIER_assert`. The run definition `MonoCera_unreach-call` of
  `xml/cuvee.xml` (`-teq` with the full lemma database, without
  [lemmas.dfy](lemmas.dfy)) and of `xml/cuvee-chc.xml` (`-chc`, Horn clauses
  for z3) takes them, one task set per operator.
- **MonoCera**: the TriCera build of the artifact (`tools/monocera/tricera`)
  with the artifact's options (`-heaparrays -abstractPO -onlyexq`, `-t` from
  the CPU time limit), on its own conversion `polished_tests/monocera`, with
  task definitions for the 125 SV-COMP tests next to them (the crafted tests
  have none). The tool-info module [monocera.py](../../monocera.py) is linked
  into `benchexec/tools`, like `cuvee.py`:

  ```
  ./benchmark xml/monocera.xml --tool-directory tools/monocera/tricera -r MonoCera_unreach-call -t C.unreach-call.MonoCera-Max
  ```

All runs: Cuvée 0.40.0, 15 min CPU time, 7 GB, 2 cores (the two hardware
threads of one core of an Intel Core i9-9900 @ 3.10 GHz), Oct 12, 2026,
`results/{cuvee,cuvee-chc,monocera}.2026-10-12_09-5*`. The paper's limits
were 300 s wall time and 2700 s CPU time on an AMD Opteron 2220 with 6 GB.

## Comparison

| Operator | tests | MonoCera (paper) | MonoCera | Cuvée `-teq` | Cuvée `-chc` | TriCera, CPAchecker, SeaHorn (paper) |
|---|--:|--:|--:|--:|--:|--:|
| forall | 93 | 27 | 26 | 53 | 0 | 0, 1, 0 |
| max | 4 | 2 | 0 | 2 | 0 | 0, 0, 0 |
| min | 11 | 3 | 3 | 7 | 0 | 0, 0, 0 |
| sum | 17 | 10 | 10 | 17 | 0 | 0, 0, 0 |
| total | 125 | 42 | 39 | 79 | 0 | 0, 1, 0 |

- The columns of the paper count the verified tests of its original logs;
  they agree with the paper. No tool gives a wrong result.
- **Time**: all proofs of MonoCera end within 300 s (at most 164 s, median
  30 s), those of Cuvée `-teq` within 20 s (median 9 s), which proves the same
  79 tests with 60 s. The 15 minutes add nothing to either.
- **MonoCera against the paper**: 3 tests fewer, `max/condn` (129 s in the
  paper), `max/sanfoundry_27_ground` (285 s), `forall/partial_lesser_bound-1`,
  none more; on a faster machine, so its search seems to behave differently
  (Java 21 here, the artifact's VM older). The other runs end by timeout (74)
  or `unknown` (12).
- **Cuvée against MonoCera**: 23 tests are proved by both, 56 by Cuvée only,
  16 by MonoCera only, 95 of the 125 by either. Those of MonoCera only are
  the strided and backward stores of `array-tiling` (`forall/nr2`-`nr5`,
  `pnr2`, `pnr3`, `pr2`, `pr3`, `rewnifrev`, `rewnifrev2`, `min/rewnifrev`),
  `forall/array_init_nondet_vars`, `array_init_var_plus_ind3`,
  `simple_array_index_value_2`, and `standard_vararg_ground` (`forall`,
  `min`). All 17 `sum` tests are proved by Cuvée, 10 of them by MonoCera.
- **Cuvée `-chc`** proves none: 120 timeouts, 3 `unknown`, 2 `arrays of
  pointers are not supported` (`array_ptr_partial_init`,
  `partial_lesser_bound`). z3's Horn solver does not find the quantified
  invariants over arrays that the tests need (`forall/eqn1` needs
  `b[k] == k*k + k + 1` for all `k < i`), as TriCera in the paper; the
  clauses are right, z3 refutes a variant of `eqn1` with a false assertion
  in 3 s. The 3 `unknown` are z3's own timeout (`-timeout 900000`).
- **Cuvée `-teq`**: 43 `unknown`, 1 timeout, 2 `arrays of pointers are not
  supported`. Of the lemmas of [lemmas.dfy](lemmas.dfy), all but
  `half_even` are in the database now (`strides.dfy`); `forall/pr2`, which
  needs it, stays open.

Earlier, with version 0.35.8 and 1 min (the former `xml/cuvee-quick.xml`),
Cuvée proved 51 tests and Cuvée+Z3 (`-fallback`) 59; the analysis of the
open goals below is of that version.

## Open goals of version 0.35.8

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
   loop modifies in place by its old contents. The lemmas below close all
   `sum` tests (see Lemmas for the open goals).
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

## Lemmas for the open goals

[lemmas.dfy](lemmas.dfy) collects lemmas for the open goals, injected by
`-include` (not part of teq.dfy, whose declarations it repeats as needed).
The generic ones among them have moved to teq.dfy, with proofs in teq.lean:
`select_current_trace_reset_add`, `select_current_trace_reset_keep`,
`stores_cases_def`, `stores_index_cases_def`, `sum_cases_below`,
`sum_mod_below`, and `div_nonpos`; the strides, the stores ahead, and
`half_even` stay in lemmas.dfy.

```
./Cuvee.sh -teq -simplify -split -simplify -include benchmarks/monocera/lemmas.dfy benchmarks/monocera/polished_tests/cuvee/sum/brs1.c
```

The results are those of version 0.35.15 with the lemmas of teq.dfy of
commit 9a13ed0f, run locally with 30 s per test. Variants of `brs1`,
`brs2`, `brs3`, `ms1`, `ms2`, and `conda` with a false assertion stay open,
since the lemmas compute the value in question or bound it only as far as
the side conditions hold.

| Test | without | with lemmas | lemma |
|---|---|---|---|
| `sum/brs1` | 1 goal | closed | `select_current_trace_reset_add` |
| `sum/ms1` | 1 goal | closed | `select_current_trace_reset_keep` |
| `sum/conda` | 1 goal | closed | `stores_cases_def` |
| `sum/s1lif`-`s5lif` | 1 goal | closed | `stores_cases_def` |
| `sum/brs2`-`brs5` | 1 goal | closed | `select_current_trace_reset_add`, `stores_index_cases_def`, `sum_cases_below` |
| `sum/ms2`-`ms5` | 1 goal | closed | `select_current_trace_reset_add`, `sum_mod_below` |
| `sum/indp5` | closed | closed | - |
| `forall/array_doub_access_init_const` | 1 goal | closed | `select_current_trace_stride2` |
| `forall/pr2` | 2 goals | closed | `div_nonpos`, `select_current_trace_stride2_cases`, `half_even` |
| `forall/rewnif` | 1 goal | closed | `select_current_trace_ahead` |
| `forall/rew`, `min/rew` | 1 goal | closed | `select_current_trace_ahead` |
| `forall/rewnifrev`, `min/rewnifrev` | 1 goal | 1 goal | `select_current_trace_ahead_down` does not match |

All 17 tests of `sum` are closed, of which MonoCera closes 10 (see above),
and 5 of the tests that only MonoCera closed before.

- `select_current_trace_reset_add` reads a sum kept in the cell `j` of an
  array (`sum[0]` of a one-element array), which the first iteration sets to
  `c` and the others increase by `G(k)`, as `current_trace_reset_add` of
  teq.dfy for a scalar; `select_current_trace_reset_keep` is the variant
  whose other iterations keep the array, since the simplifier reduces
  `sum[0] + a[i]` to `sum[0]` for `a[i] == 0` (`ms1`).
- `stores_cases_def` turns a loop that updates each position `k` once by
  cases on its old value, e.g. `a[k] == 1 ? 2 : a[k] - 1` in `conda`, into
  the stores of the values computed from the initial array, which
  `selects_stores_counter` of teq.dfy reads back. The first case stores a
  constant, since a higher-order instance must contain `a[k]`
  (`Rewrite.abstraction`).
- `select_current_trace_reset_add` needed version 0.35.15: the simplifier
  reduced the instance `(z) => a[z]` of the higher-order variable `G` to the
  array `a` by eta reduction, which left `G(k)` an application of the array.
- `stores_index_cases_def` turns a loop that stores at each position `k`
  a constant chosen by cases on `k`, e.g. `i % 2 == 0 ? 2 : 0` in `brs2`,
  into the stores of these values, which `current_stores` of teq.dfy reads
  back; then the sum consists of terms `0`, `c`, or `d`.
- `sum_cases_below` bounds such a sum of `n` terms by `e` if `0 <= e`,
  `n*c <= e`, and `n*d <= e` (`brs2`-`brs5`), `sum_mod_below` a sum of
  remainders `k % m` by `e` if `0 < m` and `n*(m - 1) <= e` (`ms2`-`ms5`).
  Their left-hand sides are comparisons, whose constants bind the bound;
  `sum_below_prefix` of teq.dfy does not apply, since its bound occurs only
  in the side condition `below_prefix(...)`, which would have to be a fact.
- `select_current_trace_stride2` reads the cells of a loop whose iteration `k`
  stores constants at `2*k` and `2*k + 1`: disjoint pairs, which cover
  `0, ..., 2*n - 1`, outside of which the initial array remains;
  `select_current_trace_stride2_cases` is the same for three cases whose
  guards do not depend on the iteration (`MINVAL` in `pr2`), with the side
  condition that they are exhaustive, without which the update would be
  unspecified where none holds. Strides of 3, 4, and 5 (`pr3`-`pr5`) and
  writes by an inner loop (`nr*`) would need lemmas of their own.
- `div_nonpos`, `x / c <= 0` exactly if `x < c` for `0 < c`, refutes the
  case `CELLCOUNT / 2 <= 0` of `pr2`. `half_even` works around a limitation
  of the simplifier: for `n == CELLCOUNT / 2` and `CELLCOUNT % 2 == 0`, the
  case `2*n <= i < CELLCOUNT` outside of the stores stays, since the
  simplifier inlines solutions of arithmetic equations into polynomials only
  and does not relate `n` to the atom `CELLCOUNT / 2` (see TODO.md); the
  lemma states the half of an even number as `CELLCOUNT == 2*n`, a
  polynomial equation, which it solves.
- `select_current_trace_ahead` reads the cells of a loop whose iteration `k`
  stores `F(k)` ahead at `k + 1` and then `G(k)` at `k`, except in the last
  one: `G(j)` remains at `j < n`, which the iteration `j` writes last. The
  side condition `n <= m` makes the guards `k + 1 < m` and `m == k + 1`
  cover all iterations.
- Open: `select_current_trace_ahead_down`, the same for the loop down from
  `s` of `rewnifrev` (`counter(s, -1, n)`, storing ahead at `i - 1`), does
  not match its trace, although the printed lemma and the trace in the goal
  have the same form, with the counter `I == counter(n + i, -1, n)` of the
  exit `i`, which only the hypothesis `0 == i + 1` determines. Not the
  cause: another rule rewriting the trace first (the log of `-debug rewrite`
  shows none), the unused first dependency (a variant without it does not
  match either), or the literal `-1` (teq.dfy matches `counter(i, -1, n)`).
  Minimal Dafny functions with the trace are no test: identical dependencies
  are merged into one, simple stores are folded into `stores` before, and
  lemma statements are not simplified. Finding the cause needs tracing the
  match in `Rewrite`.
