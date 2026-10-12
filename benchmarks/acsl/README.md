# SV-COMP tasks with ACSL annotations

The tasks of the SV-COMP categories ReachSafety-Arrays and ReachSafety-Loops
with the property `unreach-call`, annotated by hand with ACSL: loop
invariants, contracts, and logic functions, such that Cuvée can check the
expected verdict `true` by verification conditions (`-vcgen -z3 -verify`).

- **838 tasks**, 303 of Arrays and 535 of Loops, all expected `true` (the
  323 tasks expected `false` are removed). All have the contracts of the
  harness, 799 have loop invariants.
- **Proved with Cuvée 0.40.0: 603 of the 838 true tasks**, none wrong
  (60 s per task, Oct 12, 2026, see [Results](#results)); 682 with the
  annotations revised since, by single runs. These results predate the
  answers of `-verify` (0.41.0), under which refuted annotations of true
  tasks are wrong verdicts (see [Running](#running)); not yet rerun.

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
- The 323 tasks expected `false` are removed (their task definitions and
  programs, none shared with a true task): under `-verify` their answers
  depend on whether z3 refutes the failing assertion or an annotation, which
  says little about the annotations; 838 tasks remain, all expected `true`.

## Running

```
./Cuvee.sh -vcgen -z3 -timeout 900000 -verify benchmarks/acsl/<folder>/<task>.yml
./benchmark xml/cuvee-acsl.xml -r ACSL_unreach-call -t C.unreach-call.Arrays -T 60s
./benchmark xml/cuvee-acsl.xml -r ACSL_unreach-call -t C.unreach-call.Loops -T 60s
```

With `-verify` (since 0.41.0, see [doc/architecture.md](../../doc/architecture.md))
Cuvée answers `correct`, `incorrect`, or `unknown`, which
[cuvee.py](../../cuvee.py) maps to `true`, `false`, and `unknown`. The
annotations are the specification: a goal that z3 refutes (`Sat`) is
`incorrect`, also if the annotation holds but is too weak, so a true task
with a weak or wrong annotation ends as a wrong `false`. `Unknown` of z3 is
`unknown`. Without `-verify`, `-vcgen -z3`
prints the goals that do not hold, `(error "goal does not hold" "Sat"
...)`, and `-split` before `-z3` makes each annotation a goal of its own,
which locates a failing one.

Refutations are not always counterexamples: `1 << k`, `&` and the other
bitwise operators on values other than truth values are uninterpreted
functions (`shl`, `bitand`, ...), which z3 may interpret arbitrarily, e.g.
`shl(1, 0) != 1`. Annotations over them are refuted although they hold; the
powers of 2 and 4 that were written with shifts are predicates now (see
[Annotations](#annotations)).

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
  `dijkstra-u`, `knuth`).
- **Powers of 2 and 4** (`hard-ll`, `hard2`, `divbin`, `divbin2`,
  `dijkstra-u` of `nla-digbench*`, 50 tasks) are predicates of an
  `axiomatic`, not `\exists integer k; ... p == 1 << k`, whose witness z3 does
  not find and whose shift is uninterpreted: `pow2(p)` (`Pow2`), `pow2mul(b,
  B)`, `b` is `B` times a power of 2 (`Pow2Mul`), `pow4(q)` (`Pow4`). The
  axioms are goal-directed: those that relate two powers name both as
  variables, `\forall integer p, d; pow2(p) && d == 2*p ==> pow2(d)` and
  `\forall integer p, h; pow2(p) && p != 1 && p == 2*h ==> pow2(h)`, so z3
  instantiates them only for the powers in the goal; `pow2(p) ==> pow2(2*p)`
  creates new terms with each instance, a matching loop that drowns the
  nonlinear arithmetic. The others state the bound (`pow2(p) ==> p >= 1`)
  and the parity (`pow2(p) && p != 1 ==> p % 2 == 0`), which the halving
  steps need. In `divbin2` and `divbin2_unwindbound*`, where `A` is
  unbounded, `b = 2*b` wraps to 0 once `b` is 2^31 and the first loop does
  not end: the invariants are `b == 0 || pow2(b)`, with the trusted lemma
  `pow2_wrap` (2^31 is the only power of 2 that wraps). The `unwindbound`
  variants of `divbin*` and `dijkstra-u` had two errors: `r < b` in the second
  loop, which does not hold if the first ends by the bound, and the bound of
  the counter in the second loop, which is one more, since `counter++ < N`
  increments it also when the test fails.
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
- **Not annotated** beyond the harness: the 25 outputs of the reducers
  (`*-reducer.c`, unrolled control flow with gotos) and the `*_abstracted`
  tasks without loops. `loops/lu.cmp` carries bounds only.

## Results

Cuvée 0.40.0, `xml/cuvee-acsl.xml` with 60 s per task (Oct 12, 2026,
`results/cuvee-acsl.2026-10-12_09-01-*`, with the false tasks since removed):
the tasks proved per folder.

| folder | tasks | proved |
|---|--:|--:|
| array-cav19 | 13 | 13 |
| array-crafted | 43 | 37 |
| array-examples | 60 | 56 |
| array-fpi | 68 | 68 |
| array-industry-pattern | 4 | 3 |
| array-lopstr16 | 2 | 1 |
| array-multidimensional | 20 | 13 |
| array-patterns | 30 | 24 |
| array-programs | 14 | 3 |
| array-tiling | 27 | 27 |
| loop-acceleration | 23 | 22 |
| loop-crafted | 8 | 5 |
| loop-industry-pattern | 4 | 1 |
| loop-invariants | 9 | 8 |
| loop-invariants64 | 1 | 1 |
| loop-invgen | 28 | 17 |
| loop-lit | 32 | 26 |
| loop-new | 11 | 7 |
| loop-simple | 6 | 6 |
| loop-zilu | 27 | 27 |
| loops | 36 | 30 |
| loops-crafted-1 | 44 | 34 |
| nla-digbench | 26 | 16 |
| nla-digbench-scaling | 280 | 137 |
| reducercommutativity | 22 | 21 |
| **total** | **838** | **603** |

Before the support of logic functions (0.39.5, with the memory clauses and
the labels of the first annotations) 534 were proved. After this run, the
annotations of 79 tasks were revised and prove by single runs with the
options of the benchmark (`-vcgen -timeout 900000 -z3`, 60 s, Oct 12, 2026,
0.40.0 and 0.40.1):
the seven reducers with the assertion above (`array-crafted` 43,
`reducercommutativity` 22); `loop-acceleration/diamond_2-2` (for odd `y` one
iteration takes `x` from 0 to 2^32-5); `loop-crafted/simple_array_index_value_4`
(the invariants of the first loop hold also if it is not entered);
`loop-new/count_by_k` (`i % k == 0` instead of an existential);
`loop-invariants/bin-suffix-5` (the lemma above); `loops-crafted-1/theatreSquare`
(the quotients as invariants); the 15 tasks of `hard-ll` and `hard2`, the 8
of `divbin2` and `divbin2_unwindbound`, the 7 of `divbin2_valuebound`, and
the 7 of `divbin_valuebound` (predicates instead of shifts, with `-verify`,
0.41.4); 30 refuted annotations corrected (0.41.4): `y >= 0` in the second
loop of `loops-crafted-1/mono-crafted_1`, `3`, `7`, `13`, `14`; `0 <= j` in
`sum_by_3*`, where the `int j` is compared with the unsigned `n`; the last
loop of `in-de42` modulo 2^32, where `z` reaches `2*n`; in
`array-multidimensional/init-non-constant-2-n-u` and `3-u` the elements as
values modulo 2^32, `A[i][j] == (i + j + C) % 4294967296`, instead of their
differences modulo 2^32, which do not bound them, and in `2-n-u` negative
`q`, `s`; `nla-digbench-scaling/geo*-ll_valuebound*` (12), whose `long long`
are signed, with exact equalities instead of modulo 2^64;
`hard-u_valuebound*` (6) with exact equalities, `pow2(p)`, and bounds that
exclude the wrap-around; `prodbin-ll_unwindbound50`, `100`, whose `y` is 0
before the bound ends the loop, `y < p2(31 - counter)` with `p2(k) = 2^k`.

## Open

**Under `-verify`.** A sample with 0.41.3 (60 s, Oct 12, 2026) answers
`correct` for the 10 tasks proved in the run above. Of the 87 tasks with a
refuted goal in that run (`unknown` then), 69 are revised and prove (the
shifts, see [Annotations](#annotations), and the annotations corrected above),
13 end as timeouts instead (`divbin_unwindbound*`, 3: `b = 2*b` may wrap to
values that are no multiples of `B` by a power of 2; `dijkstra-u*`, 10: the
invariants modulo 2^32 bound neither `p` nor `q`, so z3 cannot exclude that
the asserted `2*p + q` wraps, 28 of the 382 goals of `-split` are `unknown`,
and a proof needs integer invariants with bounds, `q <= 4*n`, `p*p <= n*q`, of
degree 3), and 5 are wrong `false` answers by the causes below (`heavy-2`,
`matrix-1`, `veris.c_sendmail_tTflag_arr_one_loop`, uninitialized locals;
`data_structures_set_multi_proc_*`, arrays as values). Cuvée could answer
`unknown` to refutations through uninterpreted operators (see
[TODO.md](../../TODO.md)).

The 156 tasks that are not proved (235 of the run above, less the 79
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
- **Timeouts and `Unknown` of z3** (in the run above; not analyzed per goal
  yet, a timeout may also hide a matching loop or a weak annotation, as in
  `divbin2`): nonlinear arithmetic in `nla-digbench*` (`lcm1`, `lcm2` 23,
  `geo1/2/3-ll` 32 with `unsigned long long`, `prod4br-ll` 7, `prodbin-ll` 2,
  `divbin_unwindbound` 3, `dijkstra-u` 10); `array-programs/partial_mod_count_2-5`,
  integer division; `array-patterns/array26`, the parity of a count, `array1`,
  `3`, `4`, `6`, `7`, the lemmas with products and remainders;
  `array-multidimensional/add-2-n-u`, `add-3-n-u`, `diff-2-n-u`, `diff-3-n-u`,
  `copy-partial-3-u`, unsigned elements.
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
