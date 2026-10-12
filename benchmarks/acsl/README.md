# SV-COMP tasks with ACSL annotations

The tasks of the SV-COMP categories ReachSafety-Arrays and ReachSafety-Loops
with the property `unreach-call`, annotated by hand with ACSL: loop
invariants, contracts, and logic functions, such that Cuvée can check the
expected verdict `true` by verification conditions (`-vcgen -z3`).

- **1161 tasks**, 422 of Arrays and 739 of Loops; 838 expected `true`, 323
  `false`. All have the contracts of the harness, 1119 have loop invariants.
- **Proved with Cuvée 0.40.0: 603 of the 838 true tasks**, none wrong
  (60 s per task, Oct 12, 2026, see [Results](#results)); 615 with the
  annotations revised since, by single runs.

## Origin

Copied from `sv-benchmarks/c/<folder>` (the sets `Arrays.set` and `Loops.set`
of [sv-benchmarks](https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks),
checkout of Dec 23, 2025) with their task definitions and licenses, in the
same folder layout. The task definitions keep only the `unreach-call`
property, which [properties/unreach-call.prp](properties/unreach-call.prp)
states; the 225 tasks of these folders with other properties only are not
copied. Changes since (Oct 12, 2026):

- The 37 tasks whose programs use structs are removed, which Cuvée's C does
  not support (`array-industry-pattern/array_of_struct_*`, most of
  `array-lopstr16`, `loop-industry-pattern/aiob_*` and `ofuf_*`,
  `loops/bubble_sort-2`, `n.c24`, the two `verisec_OpenSER` tasks,
  `loops-crafted-1/discover_list`, `net_reset`, `array-examples/relax-2-2`).
- The allocations of sv-benchmarks ada89e0473b (unchecked `malloc` and
  `calloc` replaced by `safe_malloc` and `safe_calloc`) are merged into the
  166 files they touch, with the annotations unchanged.

## Running

```
./Cuvee.sh -vcgen -z3 benchmarks/acsl/<folder>/<task>.c
./benchmark xml/cuvee-acsl.xml -r ACSL_unreach-call -t C.unreach-call.Arrays -T 60s
./benchmark xml/cuvee-acsl.xml -r ACSL_unreach-call -t C.unreach-call.Loops -T 60s
```

No output means that all goals hold, the task is `true`. A goal that z3
does not prove, `(error "goal does not hold" "Sat" ...)` or `"Unknown"`, is
`unknown` ([cuvee.py](../../cuvee.py)): it may be a weak annotation as well
as a violation, so tasks expected `false` end as `unknown` or timeouts, never
as `false`.

## Annotations

The annotations were written by judgement, without a verifier, in the
semantics of Frama-C/WP: mathematical integers in annotations, the C types of
the program variables implicit. They were not checked with Frama-C. Each file
starts with `// ACSL annotations added by hand (benchmarks/acsl/README.md)`,
followed by a note where they need explanation.

- **Harness**, added mechanically: `reach_error` requires `\false`, so that
  every call to it must be unreachable; `__VERIFIER_assert(cond)` requires
  `cond != 0`; `abort`, `exit`, `__assert_fail` ensure `\false`, which makes
  `assume_abort_if_not` and `__VERIFIER_assume` assumptions (`ensures cond !=
  0`); `__VERIFIER_nondet_*` assign nothing.
- **Loops** get `loop invariant`s and `loop assigns` (`a[0..N-1]`,
  `a[i][0..n-1]`). The loops that rotate an array refer to its values at the
  entry by `\at(e, LoopEntry)`.
- **Functions** other than `main` get contracts where the caller needs them
  (`requires`, `assigns`, `ensures`). Globals that a function reads are
  constrained in its precondition (`requires n == 5`), since a contract does
  not see their initial values.
- **No memory clauses** (`\valid`, `\valid_read`, `\separated`, `\null`,
  `reads`): arrays are values in Cuvée's C.
- **Unsigned arithmetic** that wraps around is stated modulo its type
  (`sn == (2*x) % 4294967296`; `nla-digbench/geo*`, `lcm*`, `hard-u`,
  `dijkstra-u`, `knuth`); powers of 2 and 4 by shifts (`\exists integer k;
  0 <= k <= 64 && p == 1 << k`).
- **Sums and folds** are logic functions in an `axiomatic`, defined
  recursively over the length with the step backwards, `n > 0 ==> f(a, n) ==
  f(a, n-1) + a[n-1]`, whose instances z3 finds (the forward step `f(a, n+1)`
  has no trigger, as `+` is interpreted):
  - `asum`, `sqsum` (`array-patterns`), `rsum` of a row and `msum` of the
    first rows of a matrix `int **a` (`array-patterns`), `sum`
    (`array-crafted/zero_sum*`), `cnt` (`loops/vogal-1`);
  - `fold` for the reducer programs of `array-crafted` and
    `reducercommutativity`, with the lemmas `fold_swap` and `fold_rotate` over
    two arrays `x1`, `x2`: the invariance under the swap of the first two
    elements and under a rotation; the global `N` of `rangesum` is a parameter
    of its `fold`;
  - a final bound that follows from an element-wise property is a `lemma`
    (`array-patterns`, `total`, `asum_update`). Lemmas are trusted (`:free`),
    since their proofs need induction.
- **Bitwise operators** on values other than truth values are uninterpreted;
  a trusted `lemma` states the bits that an invariant fixes
  (`loop-invariants/bin-suffix-5`: `x % 8 == 5 ==> (x & 5) == 5`).
- **Assertions** (`//@ assert`) split a proof: they are hypotheses of the
  goals after them (since 0.40.1, `A && (A ==> B)` as in Frama-C/WP). In the
  reducers `bAnd5`, `bor5`, `xor5`, `mapavg2`, `mapavg3`, `mapsum3`,
  `reducercommutativity/sum40-2`, `//@ assert ret2 == ret;` after the second
  call separates the instances of `fold_swap` and `fold_rotate`, which z3
  does not find together. Facts about the loops of
  `loops-crafted-1/theatreSquare` (the quotients `i == (n + a - 1) / a`) are
  invariants of the later loops.
- **Counts** in `array-programs` are closed forms with integer division and
  `\min`.
- **Tasks expected `false`** get the invariants that do hold (often those of
  the `true` variant) and a note on why the assertion fails.
- **Not annotated** beyond the harness: the 25 outputs of the reducers
  (`*-reducer.c`, unrolled control flow with gotos) and the `*_abstracted`
  tasks without loops. `loops/lu.cmp`, `ludcmp`, and the verisec tasks carry
  bounds only.

## Results

Cuvée 0.40.0, `xml/cuvee-acsl.xml` with 60 s per task (Oct 12, 2026,
`results/cuvee-acsl.2026-10-12_09-01-*`): the true tasks proved per folder.

| folder | tasks | true | proved | false |
|---|--:|--:|--:|--:|
| array-cav19 | 13 | 13 | 13 | 0 |
| array-crafted | 43 | 43 | 37 | 0 |
| array-examples | 88 | 60 | 56 | 28 |
| array-fpi | 137 | 68 | 68 | 69 |
| array-industry-pattern | 9 | 4 | 3 | 5 |
| array-lopstr16 | 2 | 2 | 1 | 0 |
| array-multidimensional | 20 | 20 | 13 | 0 |
| array-patterns | 37 | 30 | 24 | 7 |
| array-programs | 16 | 14 | 3 | 2 |
| array-tiling | 29 | 27 | 27 | 2 |
| loop-acceleration | 43 | 23 | 22 | 20 |
| loop-crafted | 9 | 8 | 5 | 1 |
| loop-industry-pattern | 4 | 4 | 1 | 0 |
| loop-invariants | 10 | 9 | 8 | 1 |
| loop-invariants64 | 1 | 1 | 1 | 0 |
| loop-invgen | 29 | 28 | 17 | 1 |
| loop-lit | 32 | 32 | 26 | 0 |
| loop-new | 11 | 11 | 7 | 0 |
| loop-simple | 8 | 6 | 6 | 2 |
| loop-zilu | 27 | 27 | 27 | 0 |
| loops | 59 | 36 | 30 | 23 |
| loops-crafted-1 | 53 | 44 | 34 | 9 |
| nla-digbench | 29 | 26 | 16 | 3 |
| nla-digbench-scaling | 424 | 280 | 137 | 144 |
| reducercommutativity | 28 | 22 | 21 | 6 |
| **total** | **1161** | **838** | **603** | **323** |

Before the support of logic functions (0.39.5, with the memory clauses and
the labels of the first annotations) 534 were proved. After this run, the
annotations of 12 true tasks were revised and prove by single runs with the
options of the benchmark (`-vcgen -timeout 900000 -z3`, 60 s, Oct 12, 2026,
0.40.0 and 0.40.1):
the seven reducers with the assertion above (`array-crafted` 43,
`reducercommutativity` 22); `loop-acceleration/diamond_2-2` (for odd `y` one
iteration takes `x` from 0 to 2^32-5); `loop-crafted/simple_array_index_value_4`
(the invariants of the first loop hold also if it is not entered);
`loop-new/count_by_k` (`i % k == 0` instead of an existential);
`loop-invariants/bin-suffix-5` (the lemma above); `loops-crafted-1/theatreSquare`
(the quotients as invariants).

## Open

The 223 true tasks that are not proved (235 of the run above, less the 12
revised since), by cause:

- **Not supported by Cuvée** (57):
  - gotos to labels whose statement falls through, in the outputs of the
    reducers (26: `loop-invgen` 11, `loop-lit` 6, `loop-new` 3,
    `loop-industry-pattern/mod3.*` 3, `loop-crafted` 2,
    `array-examples/standard_sentinel.i.v+cfa-reducer`);
  - floating point (21: `nla-digbench-scaling` 19, `nla-digbench/knuth`,
    `loops/lu.cmp`);
  - `\min` (7: `array-programs/partial_mod_count_limited_*`);
  - arrays of pointers (`array-industry-pattern/array_ptr_partial_init`,
    `array-lopstr16/partial_lesser_bound`), pointer arithmetic
    (`loops/veris.c_NetBSD-libc_loop`).
- **Nonlinear arithmetic**, z3 times out or answers `Unknown` (most of the
  143 of `nla-digbench-scaling`; `nla-digbench/geo*-ll`, `lcm1`, `lcm2`,
  `prod4br-ll`, `hard-ll`, `divbin2`, `dijkstra-u`;
  `array-programs/partial_mod_count_2-5`, integer division;
  `array-patterns/array26`, the parity of a count; `array1`, `3`, `4`, `6`,
  `7`, the lemmas with products and remainders).
- **Unsigned arithmetic modulo 2^32**: `array-multidimensional/*-u` (7),
  `loops-crafted-1/mono-crafted_*`, `in-de42`, `sum_by_3*`.
- **The arrays as values**: `array-examples/sanfoundry_43_ground` assigns an
  array parameter for its caller, which needs in/out parameters (see
  [TODO.md](../../TODO.md)); `data_structures_set_multi_proc_*` (2) pass
  arrays to functions that change them.
- **Uninitialized unsigned locals** in the `loop assigns` of a loop:
  Cuvée checks the ranges of the unsigned variables that a loop modifies at
  its entry, but does not assume an uninitialized local in the range of its
  type (see [TODO.md](../../TODO.md)); `loops/vogal-1`, `heavy-2`,
  `matrix-1`, `veris.c_sendmail_tTflag_arr_one_loop` prove with the locals
  initialized.
- **A bug of the frontend**: `loops-crafted-1/watermelon` declares the
  globals `int true = 1; int false = 0;`, which reach z3 under these names
  and clash with its constants (a solver error, see [TODO.md](../../TODO.md)).

The issues of Cuvée's ACSL support are tracked in [TODO.md](../../TODO.md),
section "C frontend", item "ACSL on SV-COMP".
