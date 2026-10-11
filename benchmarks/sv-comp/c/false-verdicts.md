# Why other verifiers find expected-true tasks false

The runs of October 10, 2026 (`results/*.2026-10-10_16-44-*.Unbounded.*`,
15 minutes, all tasks of [c.set](c.set)) gave the verdict false to 222 tasks,
150 of which are expected to be false. This document covers the other 72,
which are expected to be true, and assumes that the other verifiers are right.

The evidence comes from:

- the witnesses of CPAchecker and Symbiotic (`results/<tool>.*.files/.../witness.yml`), which give the
  values of the nondet calls;
- the counterexamples in the logs of UAutomizer;
- reading each program next to its original in `sv-benchmarks`, for the
  verdicts of AISE and Korn, which have no values.

The tasks are unbounded versions of the originals: the translations to Dafny
replace concrete bounds by symbolic ones (see the [README](README.md)). In
almost every case, the numeric bounds are needed after all. They fail in
three ways:

1. **The property depends on the constant** (15 tasks). These are false even
   with mathematical integers. The expected verdict true of their Dafny
   translations is wrong as well.
2. **Values overflow** (19 tasks). The translations drop the originals'
   bounds on inputs (`if (!(n < 1000000)) return 0;`), or change `unsigned`
   or `long long` to `int`. In 32-bit `int`, the arithmetic then overflows.
   The Dafny translations remain correct with mathematical integers, which is
   why Cuvée proves 3 of these tasks.
3. **Arrays outgrow the address space** (29 tasks). [arrays.py](arrays.py)
   sizes the arrays by a fresh `N` that has only lower bounds. The tasks are
   ILP32, so `int a[N]` has more than 2^31 bytes for N ≥ 2^29 and wraps
   around 2^32 bytes at N = 2^30, `int A[N][N]` at N = 2^15, and
   `int A[N][N][N]` at N = 2^10. Separate arrays then overlap: in UAutomizer's
   counterexamples, `A`, `B` and `C` have the same address `{33}`. Writes to
   one array then overwrite the others. The originals have constant sizes or
   sizes below 2^15 (`__VERIFIER_nondet_short()`). Cuvée proves 2 of these
   tasks.

For 9 tasks with the verdict false from AISE alone, I find no cause (group
4). In all of AISE's runs, its first stage failed (`bin/runexec: No such
file or directory`), so its verdicts come from the KLEE fallback.

The runs predate [nondet.py](nondet.py), which initializes the local
variables. Of the 72 tasks, only array_of_struct_single_elem_init depends on
an uninitialized variable (`x`), as far as I have read them, and it is
false for other reasons as well.
Cuvée's own verdicts are those of the 15-minute run of the same day.

## 1. The property depends on the constant

| Task | False with | Witness | Original |
|---|---|---|---|
| array-programs/partial_mod_count_1 | CPAchecker, UAutomizer | N = 1 | `N = 1000000`; `j < N/2` is `0 < 0` for N = 1 |
| array-programs/partial_mod_count_2 | CPAchecker, UAutomizer | N = 1 | `N = 1000000`, `j < N/4` |
| array-programs/partial_mod_count_4 | all five | N = 1 | `N = 1000000`, `j < N/8` |
| array-programs/partial_mod_count_5 | all five | N = 1 | `N = 1000000`, `j < N/10` |
| array-programs/partial_mod_count_limited_2 | AISE, CPAchecker, Korn, Symbiotic | N = 5, lim = 1 | `N = 1000`; j reaches `N/(2*R)` = 1 at i = 4 |
| array-programs/partial_mod_count_limited_4 | AISE, CPAchecker, Symbiotic | N = 9, lim = 1 | `N = 1000` |
| array-programs/partial_mod_count_limited_5 | AISE, CPAchecker, Korn, Symbiotic | N = 11, lim = 1 | `N = 1000` |
| array-programs/partial_mod_count_limited_gen | AISE, CPAchecker, Symbiotic | N = 7, lim = 2, R = 2 | `N = 1000` |
| loop-lit/as2013-hybrid | CPAchecker, UAutomizer | N = 1 | `j < 10`; i counts up to 10, `i <= N` needs N ≥ 10 |
| loops-crafted-1/mono-crafted_9 | CPAchecker, UAutomizer | N = 1 | `x < 1000000`; `y == x` needs N ≥ 500000 |
| loop-zilu/benchmark52_polynomial | CPAchecker, UAutomizer | N = 1, i = -1 | `i * i < 100`; `i == 10` needs N = 100 |
| loops-crafted-1/nested3-1 | CPAchecker, UAutomizer | N = 4 | `0x0fffffff`, odd and not a multiple of 4; `z % 4 != 0` and `y % 2 != 0` need that |
| loops-crafted-1/nested3-1_abstracted | CPAchecker, UAutomizer | N = 4 | as nested3-1 |
| loops-crafted-1/nested5-1 | CPAchecker, UAutomizer | M = 4, N = 1 | `v < 10`; `v % 4 != 0` needs M not a multiple of 4 |
| array-industry-pattern/array_of_struct_single_elem_init | CPAchecker, UAutomizer | N = 3, x = 0 | 100000 elements; `p[3] = 30` and `n[3] = 40` write out of bounds for N ≤ 3 |

## 2. Values overflow

| Task | False with | Witness | Original |
|---|---|---|---|
| loop-invgen/NetBSD_loop | CPAchecker, Symbiotic | M = 2147483647 | `MAXPATHLEN < 2147483647`; `p <= M` always holds, p overflows; **Cuvée: true** |
| loop-new/half | CPAchecker, Symbiotic | k = 2^30 | `-1000000 <= k <= 1000000`; `2 * k` overflows; **Cuvée: true** |
| loop-new/count_by_k | CPAchecker | k = 8 | the bound `1000000 * k` became `N * k`, which overflows for large N; **Cuvée: true** |
| loop-lit/gsv2008 | CPAchecker, Symbiotic | y = 2147483647 | `-1000 < y < 1000000`; `y + 1` overflows |
| loop-invgen/nest-if3 | CPAchecker, Symbiotic | l = 2147483647, n = 3 | `l < 1000000`, `n < 1000000`; `l + 1` overflows, then `1 <= i` fails |
| loop-invgen/seq-3 | CPAchecker, Symbiotic | n0 = -2147483646 | `-1000000 <= n0, n1 < 1000000`; `n0 + n1` overflows |
| loop-invgen/heapsort | CPAchecker, Symbiotic | n = 2^30 | `n <= 1000000`; `2 * l` overflows |
| loop-invgen/nested9 | CPAchecker, Symbiotic | n = 2^30 | `-1000000 < n, m, l < 1000000`; `3 * n` overflows |
| loop-invgen/MADWiFi-encode_ie_ok | CPAchecker, Symbiotic | ielen = 2147483646 | `< 1000000` on all inputs; `2 * ielen` overflows |
| loops/eureka_01-2 | AISE, Symbiotic | a weight of 2147482749 | constant weights 0 to 19; `distance[y] + Weight[j]` overflows |
| array-cav19/array_init_nondet_vars | CPAchecker, Symbiotic | k = 2147483646 | `0 < j, k < 10000`, `n < 100000`; `i + j + k` overflows |
| array-cav19/array_min_and_copy_shift_sum_add | CPAchecker, Korn, Symbiotic | j = -268435457 | `-10000 < j, N, a[i] < 10000`; `a[i] - j` and k overflow |
| loops-crafted-1/mono-crafted_6 | CPAchecker | none | `x < 1000000`; `N == 8 * K` overflows to a negative N for K ≥ 2^28, the loop does not run |
| loop-invariants/linear-inequality-inv-a | CPAchecker | M = 46592, n = 0 | `unsigned char`, bound 65025; `M * M` overflows |
| loop-invariants/linear-inequality-inv-c | CPAchecker | M = 46592, n = 0 | `unsigned short`; `M * M` overflows |
| loop-invariants64/linear-inequality-inv-d | CPAchecker | n = 1, v = 3 | `unsigned long s` (LP64); `M * M` wraps below s |
| loop-industry-pattern/mod3 | CPAchecker, Symbiotic | x = 2147483647 | `unsigned int x`, which wraps to 2^32 ≡ 1 (mod 3); as `int`, `x + 2` becomes negative and `x % 3` negative |
| nla-digbench/hard-ll | AISE, CPAchecker, Symbiotic | A = 1431655766 | `unsigned int A, B`, `long long r, d, p, q`; `2 * d` overflows |
| loop-acceleration/underapprox_1-2 | CPAchecker | none | `unsigned y`, `x < 6`; `y = 2^N` wraps to 0 for N ≥ 32, and `0 % 3 == 0` |

## 3. Arrays outgrow the address space

| Task | False with | Witness | Original |
|---|---|---|---|
| loops/sum_array-2-2 | UAutomizer | M = 1, N = 2^30; A, B, C at `{33}` | size `M <= 1000000`; **Cuvée: true** |
| array-tiling/revcpyswp2 | CPAchecker | S = 3, N = 1073462785 | `SIZE < 100000`, four arrays; **Cuvée: true** |
| array-patterns/array4_pattern | AISE, UAutomizer | ARR_SIZE = 1, N = 2^30; array1, array2 at `{34}` | `ARR_SIZE` a `short` |
| array-patterns/array5_pattern | UAutomizer | ARR_SIZE = 1, N = 2^30 | `short` |
| array-patterns/array6_pattern | AISE, UAutomizer | ARR_SIZE = 3, N = 2^30 | `short` |
| array-patterns/array7_pattern | AISE, UAutomizer | ARR_SIZE = 3, N = 2^30 + 2 | `short` |
| array-patterns/array8_pattern | CPAchecker, UAutomizer | ARR_SIZE = 1, N = 2^30 | `short` |
| array-patterns/array9_pattern | CPAchecker, UAutomizer | ARR_SIZE = 1, N = 2^30 | `short` |
| array-patterns/array10_pattern | AISE, CPAchecker, UAutomizer | ARR_SIZE = 2, N = 2^30 + 1 | `short` |
| array-patterns/array11_pattern | AISE, UAutomizer | ARR_SIZE = 2, N = 2^30 + 1 | `short` |
| array-patterns/array13_pattern | CPAchecker | ARR_SIZE = 2, N = 2^30 + 1 | `short` |
| array-patterns/array25_pattern | AISE, CPAchecker, Symbiotic | ARR_SIZE = 2, N = 2^30 | `short`, `int array[ARR_SIZE][ARR_SIZE]` |
| array-patterns/array26_pattern | AISE, CPAchecker, Symbiotic | ARR_SIZE = 2, N = 2^30 | `short`, two dimensions |
| array-patterns/array27_pattern | AISE, CPAchecker, Symbiotic | ARR_SIZE = 2, N = 2^30 | `short`, two dimensions |
| array-patterns/array28_pattern | AISE, CPAchecker, Symbiotic, UAutomizer | ARR_SIZE = 2, N = 2^30 | `short`, two dimensions, `long long sum` |
| array-patterns/array29_pattern | AISE, CPAchecker, Symbiotic | ARR_SIZE = 2, N = 2^30 | `short`, two dimensions |
| array-patterns/array30_pattern | AISE, Symbiotic | ARR_SIZE = 3, N = 2^30 | `short`, two dimensions |
| array-tiling/tcpy | AISE, CPAchecker, UAutomizer | SIZE = 2 or 4, N = 2^30 | constant size |
| array-cav19/array_tiling_tcpy | CPAchecker, UAutomizer | S = 2, N = 545259529 or 2^30 + 1 | constant size |
| array-multidimensional/init-non-constant-2-n-u | AISE, CPAchecker, Symbiotic | N = 2^30 | `m = 1000, n = 1500` (6 MB) |
| array-multidimensional/transpose-u | AISE, Symbiotic | N = 2^30 | `n = 1000, m = 1800` |
| array-multidimensional/add-2-n-u | UAutomizer | n = 1, N = 32768 | `m = 1000, n = 1500`; 4 · 32768² = 2^32 |
| array-multidimensional/add-3-n-u | UAutomizer | n = 1, N = 1024 | `m = 1000, n = 1500, p = 1800`; 4 · 1024³ = 2^32, though the original's 10.8 GB per array exceed ILP32 as well |
| array-multidimensional/diff-3-n-u | UAutomizer | n = 1, N = 1024 | as add-3-n-u |
| array-patterns/array1_pattern | AISE | none | `short`, two arrays; presumably the same as array4 |
| array-patterns/array2_pattern | AISE | none | `short`, two arrays; presumably the same |
| array-patterns/array18_pattern | AISE | none | `short`, two arrays; presumably the same |
| array-patterns/array20_pattern | AISE | none | `short`, two arrays; presumably the same |
| array-patterns/array23_pattern | AISE | none | `short`, two arrays; presumably the same |

## 4. AISE alone, no cause found

These programs agree with their originals in substance. For array-crafted,
the originals have the same unbounded `N` and a single array, so arrays
cannot overlap. In mapsum5 and mapavg5, `ret` is `int` instead of
`long long`, but a sum that wraps does not depend on the order of its
summands. The other tools leave these tasks open or prove them.

| Task | Remark |
|---|---|
| array-crafted/bAnd5, bor5, xor5 | bitwise operations, no overflow |
| array-crafted/mapsum5, mapavg5 | wrapping sums, independent of the permutation |
| array-examples/sanfoundry_10_ground | one array, search and shift without arithmetic on values |
| array-multidimensional/init-2-n-u | overlapping rows would still hold the same C |
| loop-lit/gj2007 | x and y stay below N; **Cuvée: true** |
| loops-crafted-1/mono-crafted_1 | x and y stay below N; **Cuvée: true** |

## Fixes

The tasks are now patched as follows. The bounds are datatype limits, 2^k - 1 from above and -2^k from below, each the
largest one that the arithmetic allows.

- **Group 1:** each task assumes the weakest condition under which the property holds.
  - partial_mod_count: simulating all N up to 20000 shows that these are correct exactly when N is a multiple of
    the divisor in the assertion, so they assume `N % 2 == 0`, `N % 4 == 0`, `N % 8 == 0` or `N % 10 == 0`.
  - partial_mod_count_limited_gen: `N % 60 == 0` suffices for all R from 2 to 5, though it is not exact.
  - as2013-hybrid: `10 <= N`; mono-crafted_9: `500000 <= N`; benchmark52_polynomial: `81 < N && N <= 100`.
  - nested3-1 and nested3-1_abstracted: N odd; nested5-1: `M % 4 != 0`.
  - array_of_struct_single_elem_init: `3 < N`.

  The Dafny translations need the same conditions.
- **Group 2:** the inputs are bounded such that the arithmetic stays within `int`.
  - Most bounds are 2^30 - 1, e.g. for `2 * k` of half; NetBSD_loop, gsv2008, nest-if3, seq-3, heapsort, nested9,
    MADWiFi-encode_ie_ok, eureka_01-2 and hard-ll are bounded the same way.
  - count_by_k: `N <= 134217727`, since k is at most 10; mono-crafted_6: `K <= 268435455`.
  - array_init_nondet_vars: j and k at most 2^29 - 1.
  - array_min_and_copy_shift_sum_add: `a[i]` and j between -32768 and 32767, as `short`, and `N <= 16383`.
  - linear-inequality-inv-a, -c and -d: `M <= 32767`, such that `M * M` fits.
  - underapprox_1-2: `N <= 30`, since y is 2^N.
  - mod3: x is `unsigned int`, as in the original, since its loop increments x without bound.
- **Group 3:** [sizes.py](sizes.py) bounds the sizes of all arrays (see the [README](README.md)).
- **Group 4:** unchanged.

