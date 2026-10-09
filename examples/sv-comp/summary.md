# SV-COMP benchmarks with `-teq`

Tasks of the categories ReachSafety-Loops and ReachSafety-Arrays, from
`sv-benchmarks/c/<folder>` (see Coverage below),
translated by hand to Dafny, in `examples/sv-comp/<folder>/<task>.dfy`. Each
file states its command line in its first line (`-teq -simplify`, some with
`-split -simplify`), its findings in its header, and its remaining goals at
its end. Their lemmas are marked `{:teq}`, so that they are not printed.

The expected results are in one database,
[expected.csv](expected.csv): the file, whether the task is safe or unsafe,
and the number of remaining goals (`error` if the run reports an error).
`./Cuvee.sh -record <file> ...` prints the rows of examples, and
`./Cuvee.sh -test examples/sv-comp/expected.csv` checks all rows (about
three minutes). The test suite `SVComp` checks them only if the environment
variable `CUVEE_SVCOMP` is set.

- `__VERIFIER_nondet_*()` is `x := *;`, an arbitrary value.
- Simple integer programs (`loop-new/count_by_1`, `loop-zilu`) are
  translated by the C frontend, `./Cuvee.sh -print dfy <task>.yml`, which
  keeps the temporaries of the nondeterministic values and the result of
  `main`.
- Pointers that are only compared with null are truth values (non-null),
  where `malloc` does not fail; the fields of structs are arrays of their own.
- `array-memsafety` and `array-memsafety-realloc` have no task with the
  property unreach-call.
- Nondeterministic loop tests are a variable that is havocked before each test.
- `sum[0]` of one-element arrays is a scalar.
- Unsigned integers are `int` with nonnegative inputs. This is faithful
  except where C wraps around (noted in `diamond_2-2`).
- Lemmas and auxiliary definitions are in the files; nothing is added to
  teq.dfy. The declarations of teq.dfy that lemmas refer to are repeated,
  since its prelude is injected after parsing.

## Results

The counts come from the remaining goals recorded at the end of the files.

| expected | outcome | teq.dfy alone | with lemmas in the file |
|----------|---------|--------------:|------------------------:|
| safe (258) | closed | 119 | 72 |
| safe | open | 49 | 12 |
| safe | error: rewriting does not terminate | 4 | |
| safe | error: crash or internal error of `-teq` | 2 | |
| unsafe (29) | open | 13 | 16 |

No unsafe task is closed; one is refuted, its goal reduced to `false`
(`array_ptr_single_elem_init-2`). The 29 unsafe tasks are mostly variants of
translated safe ones, with the same lemmas, as checks that the lemmas do not
close them; further unsafe variants are not translated. The new lemmas were
also checked against mutants of the programs; no mutant was closed.

These safe tasks remain open:
- `seq-3`: a sum of two variables in the facts is no difference constraint.
- `gsv2008`: quadratic.
- `nested-1`, `nested_2`: nested loops.
- `sumt3`: inclusion–exclusion over counts.
- `vnew1`, `count_by_k`: literal coefficients and integer division.
- `ifcomp`: a pattern with a sum over a bound variable is not matched.
- `array_doub_access_init_const`, `array_tripl_access_init_const`: facts
  with coefficients, `n < 2 * m`.
- `array_init_var_plus_ind3`: a polynomial that matches a lemma only after
  a substitution, `(n + 3) * (n + 4) / 2`.
- `array_min_and_copy_shift_sum_add`: minimum, sums of nonnegative values,
  and a case split of hypotheses.
- `array_tiling_tcpy`: a sum with a literal in a pattern position `c - k`.
- `motivex`: products of conditionals.
- `init-2-n-u`, `nr2`: nested loops.
- `array1_pattern`: sums over arrays after stores at arbitrary keys.
- `partial_mod_count_1`, `_2`, `_limited_1`: counts over maps split at a
  threshold, where the case follows from the conclusion only.
- `mapsum1`: expressions equal modulo the definitions of the context.
- `standard_vararg_ground`: an iteration constraint with an arbitrary body,
  instantiated.
- `sanfoundry_02_ground`, `standard_partition_original_ground`: rewriting
  does not terminate; `while_infinite_loop_3`: an internal error of `-teq`
  on a loop that is always left by `break`.
- `ps2-ll` to `ps4-ll`, `cohencu-ll`, `geo1-ll`, `prodbin-ll`,
  `mannadiv`: non-linear invariants, sums of squares and cubes, powers.
- `in-de31`, `trex03-2`, `iftelse`, `vnew2`, `sumt4`, `mono-crafted_6`:
  facts over several variables, the case of the last iteration, counts of
  remainders, two-phase loop variables.
- `sanfoundry_10_ground`, `standard_strcpy_original-2`: searches whose
  exit bounds the reads of a later loop.
- `ifeqn1`, `ifncomp`, `sqm-if`, `nsqm-if`: recurrences that read `a[k - 1]`
  (a sum over a bound variable in the pattern); `ncomp`: sums of squares.
- `s12if`, `s1lif`: updates by a case split on the element itself
  (higher-order patterns with reads as arguments).
- `brs2`, `ms2`: sums that reset in the first iteration.
- `eq1`: equal traces with different names of bound variables.
- `mod3`: the case of the last iteration.
- `phases_2-2`, `gr2006`, `bh2017-ex-add`: bounds at the last iteration of
  non-linear updates, two-phase counters, counters with resets.
- `half_2`, `string_concat-noarr`: facts with coefficients or sums of two
  variables; `sendmail-close-angle`: an iteration constraint over a sum
  with the bound variable.
- `mbpr2`, `pr2`, `pnr2`, `skipped`, `rewrev`: stores at `2 k` and
  `2 k + 1` with cases that are fixed per run or depend on reads of the
  array, and a backwards loop.

Rewriting does not terminate on `standard_partial_init_ground` and
`standard_partition_ground-2` (counts over prefixes), and on
`sanfoundry_02_ground` (the rule for `earlier` of a counter), and `-teq`
crashes on `diamond_2-2`.

## Coverage

All folders of `ReachSafety-Loops` and `ReachSafety-Arrays` have been
looked at; the tasks that are not translated are variants of translated
ones, or out of scope, as listed per folder:

- `array-cav19` (13 of 13), `array-lopstr16` (11 of 11).
- `array-multidimensional` (1 of 20): all are nested loops over arrays of
  rows, represented by `init-2-n-u`.
- `array-patterns` (1 of 37): all store at nondeterministic indices and
  check sums, represented by `array1_pattern`.
- `array-tiling` (14 of 29): the others tile 3 to 5 positions per
  iteration (`mbpr3`–`5`, `nr3`–`5`, `pnr3`–`5`, `pr3`–`5`), run backwards
  (`rewnifrev`, `rewnifrev2`), or repeat `array-cav19/array_tiling_tcpy`.
- `array-industry-pattern` (9 of 17): the others are variants of
  `array-lopstr16` tasks, and `check_removal_from_set_after_insertion`
  calls procedures with inner loops.
- `array-programs` (7 of 16): `partial_mod_count_3` to `_5` and
  `partial_mod_count_limited_2` to `_gen` are variants.
- `array-crafted` (5 of 43): the folds `mapsum`, `mapavg`, `bAnd`, `bor`,
  `xor` (1 to 5) are represented by `mapsum1`, the bitwise ones are not
  parsed by the Dafny frontend; the `zero_sum` variants by `zero_sum1`,
  `zero_sum_m2`, `zero_sum_const1`, `zero_sum_const_m2`.
- `array-examples` (42 of 96): the numbered variants (`standard_init3`
  to `_init9`, `standard_copy4` to `_copy9`, `standard_two_index_04` to
  `_09`) and the unsafe `-1` variants are represented by their first members;
  not translated: the sorting algorithms (nested loops and sortedness), the
  sets of `data_structures_set_multi_proc` and `relax` (procedures with
  loops), `standard_sentinel.i.v+cfa-reducer` (goto), `sanfoundry_43_ground` (no
  assertions).
- `array-fpi` (47 of 151): each family (`brs`, `cond`, `eqn`, `ifeqn`, `indp`,
  `mod`, `ms`, `ncomp`, `res`, `s*if`, `s*lif`, `sina`, `sqm`, `ss`, ...) by
  one or two members; the `f` variants are unsafe.
- `loop-invariants` (10 of 10), `loop-invariants64` (1 of 1).
- `loop-crafted` (5 of 9): `simple_array_index_value_1-2` is unsafe,
  `simple_array_index_value_4` and its reducer variants compare an array
  from both ends.
- `loop-industry-pattern` (1 of 17 with unreach-call): `aiob_*` and
  `ofuf_*` are generated control software of several hundred lines, the
  reducer variants repeat `mod3`, and `nested-3` has no unreach-call
  property.
- `loop-simple`: nested loops, represented by `nested_2`.
- `loops-crafted-1` (19 of 55): variants (`in-de32` to `_62`,
  `mono-crafted_9` and `_11` to `_14`, `sumt5` to `_9`, the `_abstracted`
  ones), nested loops (`nested3-*`, `nested5-*`, `nested_delay_*`), the
  unsafe `Mono*_1`, and large programs (`discover_list`, `net_reset`,
  `theatreSquare`, `watermelon`).
- `loops` (14 of 75): integer programs; the array, string, and sorting
  programs (`array-*`, `string-*`, `insertion_sort-*`, `bubble_sort-*`,
  `lu.cmp`, `ludcmp`, `matrix-*`, `vogal-*`, `veris*`, `eureka_*`,
  `n.c40`, `nec*`) are not translated; character arrays are not parsed
  back from the output of the C frontend.
- `loop-zilu` (22 of 27 with unreach-call): the `_abstracted` variants are
  the same programs with abstracted loops.
- `loop-new` (8 of 11): the reducer variants of `gauss_sum`.
- `loop-acceleration` (24 of 43): the unsafe `-1` variants and the
  `_abstracted` variants.
- `loop-lit` (14 of 32): nested loops (`as2013-hybrid`, `cggmp2005b`,
  `hh2012-*`) and reducer variants.
- `loop-invgen` (9 of 29): nested loops (`id_build`, `nested6`, `nested9`,
  `nest-if3`), the reducer variants, and string processing with procedures
  (`apache-*`, `MADWiFi-*`, `SpamAssassin-*`, `heapsort`).
- `loop-floats-scientific-comp`: floating point, which the translations do
  not model.
- No unreach-call tasks: `array-memsafety`, `array-memsafety-realloc`.

- `loop-acceleration`, `loop-lit`, `loop-invgen`, `loop-new`,
  `loops-crafted-1`, `loop-zilu`, `loops`: see above; their earlier
  translations are in the same folders.
- `nla-digbench` (8 of 29): non-linear invariants (`ps2` to `ps4`,
  `cohencu`, `geo1`, `sqrt1`, `prodbin`, `mannadiv`); the others are of the
  same kind (`egcd*`, `fermat*`, `bresenham`, `dijkstra`, `divbin*`,
  `hard*`, `knuth`, `lcm*`, `prod4br`, `ps5`, `ps6`, `geo2`, `geo3`).
- `nla-digbench-scaling` (0 of 424): the tasks of `nla-digbench` with
  value bounds or unwinding bounds, represented by those.

## Concepts of the lemmas

The lemmas are generic in their functions (higher-order patterns) and
constants. They are closed forms, not unfoldings of iterations or induction
steps:

- **Traces of scalars**
  - Two-phase counters: the current value, and the bound at the last
    iteration (`phases_1-1`, `Mono1_1-2`).
  - Followers (`benchmark05`), flags (`standard_compare_ground`),
    geometric sequences (`underapprox_1-2`).
  - Values that increase by positive constants (`large_const`).
  - Modular invariants (`loopv1`), interval invariants (`benchmark51`).
  - Counting remainders (`half`, `sumt2`).
  - Bounds of counters with arbitrary steps (`benchmark04`, `benchmark09`).
  - Splitting a trace whose guard is the same in all iterations
    (`diamond_1-1`).
- **Traces of arrays**
  - Recurrences over the predecessor, as initial element plus the sum of
    the added terms (`seq_init`, `eqn1`, `sqm`, `pcomp`, `nsqm`).
  - Joining two stores at the same position into one store of a conditional
    value (`running-2`, `conda`, `condm`, `array_monotonic`).
  - Guarded stores, read at a position (`copysome1-1`, `array_mul_init`,
    `array_monotonic`), and clamping (`condn`).
  - Stores of reads outside the written range (`palindrome`).
  - Reading back stores at the same counter (`ss1`).
  - Stores at several positions per iteration, `2 k` and `2 k + 1`, or
    `3 k`, ..., by the remainder (`array_doub_access_init_const`).
  - Stores from the end, at `c - k`: `occurs` and `indexof` of decreasing
    positions (`array_init_both_ends_multiple_sum`), copies from both ends
    (`array_tiling_tcpy`).
  - Joining guarded stores of the same position, polymorphic in the element
    type, e.g. pointers as truth values (`base_case`, `single_elem_safe`).
  - Prefixes of maps over counters as maps over shorter counters
    (`array_init_var_plus_ind3`).
  - Stores at `k + 1` and then at `k`, overwritten in the next iteration
    (`rew`, `rewnif`).
  - Guarded stores at positions of a counter with step 2, and `occurs`
    and `indexof` of even positions (`array_of_struct_ptr_monotonic`).
  - Copies except at one position, whose case the simplifier rewrote to a
    store at the literal position (`copysome2-1`).
  - The sum after shifting by one (`mapsum1`).
  - The maximum of the elements from position 1 on, with the element at 0
    as initial value (`sanfoundry_27_ground`).
  - Reads of stores at another counter of the same definition (`ssina`,
    `ss2`), since keys are compared literally.
  - A loop variable whose cases `i == 0` and `i != 0` agree is the counter
    (`ifeqn1`).
- **Iteration constraints**
  - A constraint is first abstracted by an atom (`agree`, `absent`,
    `!occurs`, `above`, `positive`, `below`).
  - A second lemma then takes that atom as its side condition and
    instantiates it at a witness (`find`, `sentinel`, `compare`,
    `count_by_nondet`, `simple_array_index_value_2`).
  - Side conditions that are iteration constraints themselves do not
    terminate.
  - Instantiations as comparisons with a further summand,
    `b <= earlier(j, xs) + d` (`array_init_nondet_vars`), pairwise
    constraints over two dependencies (`array_init_pair_symmetr2`), and
    constants that rewrite `earlier(j, xs)` (`flag_loopdep_simple`).
  - Bounds of the values chosen in each iteration, abstracted by `below`
    and `nonneg`, bound the sum and the last value
    (`linear-inequality-inv-a`, `-c`, `-d`).
  - A value that changes only where it differs from its initial value
    keeps it (`const`).
  - A value set to the iteration where a condition holds lies in the
    bounds of its initial value and the iterations (`gj2007b`).
  - An update `(x + c) % m` keeps the remainder modulo the divisors of `c`
    and `m` (`overflow_1-1`, since removed).
  - A search over an array with a sentinel stored at `c` stops at `c`
    (`array_4`).
  - A value that swaps two values stays one of them (`benchmark32_linear`).
  - A value that changes by `d` from iteration `c` on, a two-phase counter
    (`mono-crafted_8`).
  - A counter with a reset stays within bounds (`n.c11`).
  - A flag keeps its initial value iff its guard never holds
    (`flag_loopdep_simple`), reused with the abstraction `agree` and `-split`
    (`standard_password_ground`, `standard_compareModified_ground`,
    `standard_strcmp_ground`).
- **Arithmetic** (stated in the simplifier's normal form): parity, halving
  of even polynomials, telescoping sums, cancellation, the signs of
  `(x + x * x) / 2` and `(-x + x * x) / 2` plus a nonnegative summand.
- **Not about traces:** read over write at a different position (see
  Issues), equations of conditionals as case splits, bounds of integer
  division (`mlceu2`), the cancellations `(2 * x) / 2 == x` and
  `(3 * x) / 3 == x`, the halving of further polynomials (`eqn2`,
  `sqrt1-ll`), and
  `x % x == 0` (`modp`, `mods`).

## Issues

The issues found are in [TODO.md](../../TODO.md).

- **Bugs:**
  - Non-termination with counts over prefixes, and with comparisons as
    left-hand sides whose side conditions are iteration constraints.
  - An update cover leaves rule variables uninstantiated.
  - Equations between applications with open variables are not matched
    against the facts.
  - Sums over bound variables of combinators are not matched.
  - `-teq` crashes on many conditionals in sequence.
- **Limitations:**
  - Integer equations as lemmas rewrite terms, not atoms.
  - Rules on comparisons do not match their negations.
  - Hypotheses are not split into cases (hence `-split -simplify`).
  - No integer rounding, no cancellation of factors.
  - Literal coefficients are not matched by variables.
  - Higher-order summands match one summand only.
  - Expressions are not compared modulo the names of bound variables.
  - Facts over more than two variables are not combined, nor facts with
    coefficients.
  - Reads over writes are decided without the facts of the context.
  - Conditionals in equations and products are not lifted, and the
    branches of conditional formulas are not simplified under the facts.
  - `-split` splits `{:rw}` lemmas, too.
  - Expressions are not compared modulo the definitions of the context.
  - A pattern `c - k` does not match sums with a literal.
- **Rules of thumb:**
  - Put the lemmas that a later lemma could hide first, since rules apply
    in order.
  - Keep the matched dependencies on the right-hand side instead of
    rebuilding counters.

## Further ideas for lemmas, not realized

- **Telescoping in general:**
  `sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: F(k + 1) - F(k))) == F(n) - F(0)`.
  It would replace the specific telescoping and halving lemmas of `pcomp`,
  `eqn1` and `sqm`, but it needs matching modulo normalized polynomials.
  Also sums of `k * k` and `k * k * k` stated multiplied out, e.g.
  `6 * sum(maps(... k * k)) == 2 * n * n * n - 3 * n * n + n`, so that the
  divisions cancel.
- **Inclusion–exclusion over counts:**
  `count(true, maps(A || B)) == count(true, maps(A)) + count(true, maps(B)) - count(true, maps(A && B))`,
  and the partition `count(true, maps(A && B)) + count(true, maps(A && !B)) == count(true, maps(A))`
  (`sumt3`). This needs equality modulo the names of bound variables, or
  lemmas that keep the bound variables of the instance.
- **Classes of remainders for several moduli,** e.g. `k % 3` and `k % 2`
  combined into classes modulo 6, for counts with nested conditions (`sumt3`).
- **The last value of a trace that takes the values of a dependency:**
  `current(trace(x0, for ⌊counter(0, 1, n)⌋, ys do x, k, y :: y)) == if n == 0 then x0 else earlier(n - 1, ys)`.
  This is the outer trace of nested loops (`nested_2`), and the trace of a
  havocked loop test (`afnp2014`).
- **Composition of nested loops:** an outer trace whose iterations add the
  lengths of inner counters of a constant length `m` is `n * m` (`nested-1`,
  `nested_2`). This needs the iteration constraints over sequences of traces,
  e.g. `K₈ == counter(0, 1, n₆)` for each iteration, to be combined.
- **Instantiation of an iteration constraint at the last iteration:**
  `invs(for ⌊counter(0, 1, n)⌋, ⌊X⌋ check k, x :: P(x))` with `0 < n` gives
  `P(earlier(n - 1, ⌊X⌋))`. This generalizes the bound at the last value of
  `Mono1_1-2` and the instantiations of `count_by_nondet`, e.g. as a pair
  of abstraction and instantiation, or as a forward rule.
- **Overshoot of bounded steps:** a value that increases by at most `c` per
  iteration and whose loop test is `x < B` ends below `B + c`; with
  remainders, it ends exactly at `B` (`Mono1_1-2`, `vnew1`, `count_by_2`
  generically).
- **Iteration constraints with a coefficient:**
  `invs(for ⌊counter(0, 1, n)⌋ check k :: d * k < b) <==> n == 0 || d * (n - 1) < b`
  (`vnew1`, `count_by_k`). This needs coefficients matched by variables, or
  lemmas per literal.
- **Selection, or compaction:** stores at the positions given by a count of
  guarded iterations, e.g. `C[j] = i` where `A[i] == B[i]`. The stored values
  satisfy the guard (`standard_partition_ground-2`: `bb[x] >= 0`), and the
  stored indices are increasing, with `C[x] >= x` (`standard_partial_init_ground`).
  The non-termination of teq.dfy on these counts comes first.
- **Signs of quadratic accumulations:** the sum of `y0, ..., y - 1` is
  negative if `y <= 0` (`gsv2008`).
- **Splitting general conjunctions in iteration constraints:**
  `invs(P && Q) <==> invs(P) && invs(Q)`. Only the negated disjunction
  matched, since the simplifier keeps `!(A || B)`.
- **Scalar updates whose condition is the same in all iterations,** joined
  into one case, `trace(... case c => F(x) case !c => G(x)) == trace(... if c then F(x) else G(x))`,
  as for stores (`condm`), instead of splitting the trace (`diamond_1-1`),
  which can loop. This needs acceleration of conditional updates, or `-split`
  on the conditional of the closed form.
- **Recurrences over the predecessor at `k - 1`** (`ifcomp`), once sums over
  bound variables in patterns are matched; also clamps and followers for
  minimum and maximum of scalars.
- **Forward rules** (branch `forward`) instead of the pairs of abstraction
  and instantiation: an iteration constraint, instantiated at the terms that
  occur, e.g. `earlier(j, xs)`.
- **Not lemmas:** `seq-3` needs Fourier–Motzkin on the facts, not only
  difference constraints, and `diamond_2-2` needs the TEQ of many
  conditionals without a stack overflow.
