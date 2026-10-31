# Residual goals of the cloud run of 0.53.22

An analysis (Oct 31, 2026) of the goals that `-svcomp -rules` leaves open on the tasks with the expected verdict true,
from the log files of `all05322x5` (0.53.22 with the memo of solutions, released as 0.53.23; 300 s, one core, Xeon
E3-1230 v5). Of the 412 open tasks ([open-tasks.md](open-tasks.md)), 163 end in `unknown` with their residual goals in
the log (58 of Arrays, 105 of Loops); one representative of each program was read, the variants (`_valuebound`,
`_unwindbound`, sizes) checked for the same shape. The 174 timeouts have no goal and the 74 errors stop before
`-prove`; neither is analyzed here.

The goals are quoted as the log prints them (SMT-LIB), shortened where marked.

## Summary

| Principle | Tasks | Where | Section |
|---|---|---|---|
| induction with the iteration constraint as hypothesis | about 40 | a rule of the database, an open design question | 1 |
| the iteration constraint at the last iteration | 7 | a rule over `invs`, cost to check | 2 |
| reads of constant arrays | 3 | done: `select_const`, 3 correct locally | 3 |
| arithmetic arguments and binders compared modulo the context | 4 | engine (engine.md 1.2, section 8) | 4 |
| max and min with the tie on the other side | 3 | done in part: `maxs_tie`, `mins_tie`, 1 correct locally | 5 |
| small lemmas missing from the database | about 20 | done in part: 8 correct locally | 6 |
| counts of residues under unsigned wrap-around | 8 | database | 7 |
| arithmetic | about 35 | engine (engine.md, section 2) | 8 |
| known gaps, unchanged | about 50 | open-tasks.md, engine.md | 9 |

## 1. Induction with the iteration constraint as hypothesis (about 40 tasks)

The largest group. The program asserts a property inside its loop, so `-teq` gives it as an iteration constraint over
all earlier states (`invs` over `butlast X`), and the goal is the same property at the state after the loop, the
`current` of the trace. Nothing relates the two: the step from the last earlier state to the current one is missing.
hh2012-ex2b:

```
(=> (and (= N$11 (trace (n$5 0) ((k$9 (butlast K$10)) (tmp$6 Tmp?$7))
           (eps ((and tmp$6 (< n$5 60)) (+ n$5 1)) ((and tmp$6 (<= 60 n$5)) 0) ((not tmp$6) n$5))))
         (= n$14 (current N$11))
         (invs ((k$9 (butlast K$10)) (n$5 (butlast N$11)) (tmp$6 Tmp?$7))
           (or (and tmp$6 (< n$5 60)) (and tmp$6 (= n$5 60)) (and (not tmp$6) (<= n$5 60))))
         ...)
     (<= n$14 60))
```

The same shape, with the asserted equation of the program as the constraint and as the goal: fermat2-ll_valuebound1,
lcm2_valuebound1, mannadiv, bresenham-ll and its 6 valuebound variants (`(= (+ (* 2 Y) (* 2 Y x)) (+ X (* 2 X y) v))`),
divbin (6) and divbin2 (7), hard-ll, hard-ll_valuebound5, hard-u_valuebound5, hard2_valuebound5 (the asserted
equation as `(= (map ...) (butlast (consts n 0)))`); with a bound: mine2017-ex4.7, as2013-hybrid, bh2017-ex3 (two
components), trex03-2 (decrements of positive values), partial_mod_count_2 to 5 (`j < 249999` of a count); without a
constraint, an inductive bound of a toggle: benchmark32_linear (`x` alternates 1 and 2, goal `x <= 8`), and an
inductive residue: mod3 (`x % 3` by cases on `x % 3`).

**Principle.** A property `P` of the states that holds at every earlier state and that every case of the update
preserves holds at the current state; with no iteration, it is `P` of the initial value. As a rule on the atom of the
goal, `P(current(X))`, with the side conditions `P(x0)`, the constraint `invs(... P(x))` looked up among the facts
(`Rewrite.known`), and `P(x) ==> P(U(x))` per case, decided by the simplifier. `P` is the goal atom abstracted at the
current value (`Rewrite.abstraction`); for traces of several accumulators, at the components. With the constraint as
hypothesis, the preservation is not even needed for all `x`: it is needed only for the last earlier state, so the
side condition can assume the constraint.

This is A1 of engine.md (section 7, about 150 nla tasks in all, of which the timeouts are not checked); the goals show
that SV-COMP states the invariant as an in-loop assertion in most of them, which makes the induction hypothesis a fact.
`current_trace_bounded` (counters.dfy) is the case of an interval with exactly three cases and a keeping one; it does
not match hh2012-ex2b (three cases, no keeping case), as2013 (two), benchmark32 (two and a keeping one). Open:
whether such a rule belongs in the database, and its cost, since its left-hand side is any atom over a `current`.

## 2. The iteration constraint at the last iteration (7 tasks)

The goal needs the constraint at the last earlier state, together with the exit of the loop, not at the current one.
gsv2008:

```
(=> (and (= X$10 (sums (- 50) (map ((k$7 (butlast K$8))) (+ k$7 y$3))))
         (= (+ x$11 50) (+ (div (+ (- n$6) (* n$6 n$6)) 2) (* n$6 y$3)))
         (= y$12 (+ n$6 y$3))
         (invs ((k$7 (butlast K$8)) (x$4 (butlast X$10)) (y$5 (butlast Y$9))) (< x$4 0))
         (<= 0 n$6) (<= 0 x$11) ...)
     (< 0 y$12))
```

`x` is negative before the last iteration and non-negative after it, so the last summand `n - 1 + y` is positive.
Likewise count_by_nondet (the sum before the last value is below 1000000, each value at least 1), sendmail-close-angle
(`k + 2 != tmp` at `k = buf - 1`), half_2 (`2k < n` at `k = n - 1`), count_by_k (`k * k' < 1000000 * k` at the last
`k'`, cancelling the positive factor `k`), benchmark52_polynomial (`(k + tmp)^2 < 100` at the last `k`, then
`i^2 >= 100` with `i > -10` gives `i == 10`), theatreSquare (`(i - 1) * a < s <= i * a` for two loops that compute the
same `i`, then the equality of both; with section 8).

**Principle.** For `0 < n`, `invs` over `butlast X` is `invs` over the first `n - 1` states and the constraint at
`earlier(n - 1, X)`. `invs_counter_upper` does this for constraints over the counter alone; a general form would split
off the last element of every `invs` with a positive count, as a rule on the `invs` fact. A forward or rewrite rule
on every `invs` costs on every task; to measure. No unfolding of a trace: it splits a list.

## 3. Reads of constant arrays (3 tasks)

Global arrays of C are zero-initialized, `(as const (Array Int Int)) 0`, and `select` of it is not evaluated.
verifythis/lcp (three goals of this kind):

```
(=> (and ... (invs ((k$48 (butlast K$49)))
               (= (select ((as const (Array Int Int)) 0) (+ k$48 tmp$17))
                  (select ((as const (Array Int Int)) 0) (+ k$48 tmp$19))))
         (<= 0 tmp$63) (< tmp$63 l$51))
     (= (select ((as const (Array Int Int)) 0) (+ tmp$17 tmp$63))
        (select ((as const (Array Int Int)) 0) (+ tmp$19 tmp$63))))
```

Also verifythis/elimination_max (`(<= (select (const 0) i) (select (const 0) x))`) and loops/nec40 (`y` is the
constant array, `(not (occurs 0 (selects y ...)))` with `(= (select y i) 0)`). **Done (Oct 31):** the
rule `select_const` of teq.dfy, `const(v)[k] == v` (`const` is the function of the prelude, also in Dafny); all three
correct locally in 8 to 23 s (`-svcomp -rules`). nec40 needs no rule on `selects` of a constant array, since
`earlier_selects` reduces its reads to `select`. Test: examples/c/teq/const_array.c.

## 4. Arithmetic arguments and binders compared modulo the context (4 tasks)

- **Indices and counts written differently.** mapsum5: the two sums read the swapped array at `(+ N$4 (- 1))` and at
  `i$59` with `(= N$4 (+ i$59 1))`; the two `select` terms are not equal, since arithmetic as an argument of another
  function stays as written (engine.md 1.1). bor5 and bAnd5: `(bor (elems Tmp?$15))` against
  `(bor (elems (selects x$23 (butlast (counter 0 1 (+ n$31 1))))))` where `x$23` stores `Tmp?$15` at
  `(butlast K$18)` with `(= K$18 (counter 0 1 N$4))` and `(= N$4 (+ n$31 1))`: the read lemma of `selects` over
  `stores` at the same keys does not see that the keys are the same counter (bAnd5 the same with `band`).
  **Change:** compare arithmetic arguments modulo the classes in `eq_` and in the matcher (engine.md 1.2, "the matcher
  computes the canonical form of an arithmetic argument where a pattern needs it"); these are its first tasks.
- **Traces equal up to the names of their variables.** loop-invariants/eq1: `w` and `x` (and `y`, `z`) are traces
  with the same initial value and the same update, differing in the name of the accumulator; the goal `(= w$38 x$39)`
  stays open. Binders modulo bound names in the classes (engine.md, section 8, not done by decision); here the terms
  are definitions of two variables, so a comparison of the definitions by `Canon.equal` in `eq_` would suffice.

## 5. Max and min with the tie on the other side (3 tasks)

The folds `maxs` (`case m < v => v case v <= m => m`) and `mins` (`case v < m => v case m <= v => m`) do not match a
loop that takes the new value also at a tie. sanfoundry_02_ground (the largest element):

```
(trace (largest1$25 (earlier 1 Tmp?$13)) ((k$28 (butlast K$29)) (i$26 (butlast (counter 2 1 99998))))
  (eps ((<= largest1$25 (earlier i$26 Tmp?$13)) (earlier i$26 Tmp?$13))
       ((< (earlier i$26 Tmp?$13) largest1$25) largest1$25)))
```

loops/array-1 is the same for the minimum (`(<= tmp$13 menor$11) tmp$13`). Both cases agree at the tie, so the traces
are the folds. **Done (Oct 31):** the folds `maxs_tie` and `mins_tie` (aggregation.dfy), whose bodies take the new
value also at a tie, rewritten into `maxs` and `mins`; array-1 correct locally in 43 s (examples/c/teq/max_tie.c);
sanfoundry_02_ground not tried locally (138 s on the cloud), its goals on the second largest element stay open.
The alternative, the guards normalized where the results agree at the boundary, would be an engine change (a
directed merge as in `Simplify.eps`, engine.md 5.1). reducercommutativity/max
needs in addition that the multiset of `selects` of the function `swap` is that of the array (`elems_selects_swap`
states it for a swap written as two stores) and that `select_swap` does not rewrite the reads into cases before the
fold applies.

## 6. Small lemmas missing from the database (about 20 tasks)

Each from a residual goal. Done (Oct 31, correct locally with `-svcomp -rules`, one run each): 8 tasks. Not taken:
`selects_counter_empty` (a small example was proved without it, and its task needs 148 s), the fold `lasts`
(gj2007b timed out at 60 s with it, 31 s `unknown` before; to diagnose).

| Lemma | Tasks | Goal |
|---|---|---|
| **done**, `indexof_counter_down` | array_init_both_ends_multiple_sum (10 s); eureka_05 not tried (151 s) | `(indexof (+ (- k) 99999) (butlast (counter 99999 (- 1) 100000)))` |
| **done**, `pow_positive` | trex01-2 (9 s); the sign cases of the halving in divbin, hard not tried | `(<= 1 z$27)` with `(= z$27 (pow 2 n$23))` |
| closed `pow` evaluated | underapprox_1-2 | `(= y$11 (mod (pow 2 6) 4294967296))`, goal `(< 0 (mod y$11 3))` |
| `selects` over an empty counter, tried and dropped | array_min_and_copy_shift_sum_add (7 goals) | `(sum (elems (selects a$9 (butlast (counter 0 1 0)))))` |
| **done**, `count_length` (forward) | apache-escape-absolute (26 s), nest-if3 (32 s) | `(+ (bag.select (elems Tmp?$51) 0) c$59) = n`, goal `-1 <= c` |
| sums over the same keys add pointwise | bhmr2007 | `a` and `b` sums of `eps(c => 1, !c => 2)` and `eps(c => 2, !c => 1)`, goal `(= (+ a b) (* 3 n))` |
| a trace that keeps its initial value | const | `s` from 0 with `case s == 0 => 0`: the initial value is a fixed point of the update |
| **done**, `bxor`, `bxors` and the seeds | xor1-xor4 (18 to 19 s); xor5 has a variable size (section 4) | `bitxor` folded in two orders, as `bands`, `bors` |
| a counter that saturates at a bound | partial_mod_count_limited_1, _5 (the others time out) | `(eps ((< k tmp) (+ k 1)) ((<= tmp k) k))`, i.e. `min(k, tmp)` at iteration `k` |
| the last position where a guard holds, the fold `lasts` tried | gj2007b (timeout), sanfoundry_10_ground | `(eps ((not (= tmp 0)) k$15) ((= tmp 0) m$10))`: bounds and the guard at the position |
| an element at most the sum of non-negative ones, a sum at most count times bound | linear-inequality-inv-a, -c, -d | `(<= (earlier (- n 1) V?) (mod (sum (elems V?)) 2^32))`; the bound needs a product with the count (section 8) |
| bitwise and with a literal mask | bin-suffix-5 | `(= (bitand x 5) 5)` with `x = (8n + 5) mod 2^32`; C bitwise operators are uninterpreted (TODO.md, C frontend) |

## 7. Counts of residues under unsigned wrap-around (8 tasks)

sumt2 to sumt6 count the iterations by combinations of residues (`k % 2`, `k % 3`, `k % 4`) in unsigned variables,
sumt2:

```
(=> (and (= J$15 (trace (j$8 0) ((k$11 (butlast K$12)) (l$9 (butlast (counter 0 1 n$6))))
                   (eps ((= (mod k$11 2) 0) j$8) ((< 0 (mod k$11 2)) (mod (+ j$8 1) 4294967296)))))
         (= i$16 (div (+ n$6 1) 2)) (= j$17 (current J$15)) (<= 0 n$6) (<= n$6 20000001))
     (= (mod (+ i$16 j$17) 4294967296) n$6))
```

The conditional increment modulo `2^32` is not folded into a count (the remainder of the increment hides the step of
`current_trace_step_or_keep`); then the count of the odd numbers below `n` (`count_remainder`) and the sum below
`2^32`. sumt3 to sumt6 need the counts of guards that combine several moduli (the guards partition the iterations, so
their counts add up to `n`). Also ddlm2013 (a guard on the parity of `mods 0 2`, always even) and loopv3 (`4 * (i / 4)
== i` for a sum of 8 or 4; divisibility, set aside). iftelse is of this kind and correct locally with
`count_remainder_offset` (uncommitted). **Change:** the remainder of a conditional increment lifted out of the trace,
as `current_trace_mod_add_*` does for unconditional ones; then counts of residues of combined moduli.

## 8. Arithmetic (about 35 tasks)

- **A forward fact not available to the remainder** (engine.md 2.1): geo1-ll, geo2-ll, geo3-ll, each with 6
  unwindbound variants (18 tasks). geo2-ll_unwindbound2:
  `(= (mod (+ (* 18446744073709551615 S) (* S z) (* 18446744073709551615 (pow z 2) z) 1) 2^64) 0)` with
  `S = (current (series 1 z 1 2))`, which the forward fact `current_series` makes `0` inside the remainder.
- **Exact division** (engine.md 2.3): cohencu-ll and 6 variants.
- **Products bounded by the bounds of their factors**: nested-1 (`(<= 100 (* tmp$10 tmp$11))` from `10 <= tmp`),
  benchmark52_polynomial (squares), linear-inequality-inv-a/c/d (the sum at most `tmp * 255` with `tmp <= 255`),
  theatreSquare (`(i - 1) * a < s <= i * a` determines `i`). The simplex is linear; a product of two bounded
  variables is an atom without bounds. **Change:** bounds of a product from the signs and bounds of its factors when
  it enters the arithmetic, as the definition of `div` is (engine.md 2.4).
- **Squaring modulo 2^32 under a guard of division**: phases_2-2.
- **Floating point**: freire1 (7), out of scope.

## 9. Known gaps, unchanged

- array-patterns (30 unknown), array-multidimensional (init-3-u, copy-3-n-u, init-non-constant-3-u, transpose-u):
  open-tasks.md.
- An iteration constraint read at a witness: array_init_pair_symmetr2, array_init_nondet_vars,
  standard_vararg_ground (engine.md, section 8).
- Strided stores: nr2 (engine.md 4.2), mbpr4 and mbpr5 (the case split on `0 < i < 4`, engine.md 5.3), skipped (two
  stores per iteration with guards that read the array), rewrev (stores ahead downwards with a case), mods.
- Arrays as values: sanfoundry_43_ground (bugs.md).
- Nested loops and sorting: nested6, insertion_sort-2-2, sorting_bubblesort_ground-1, sanfoundry_02_ground's second
  largest, simple_array_index_value_4 (two `mods` traces of indices moving towards each other).
- Traces whose guards read the accumulator or another phase: gr2006 (up to 50, then down), mono-crafted_13 (a step of
  2 guarded by a `phases` trace; the parity).
- Halving with C's division of signed values (divbin, divbin2, hard): `(eps ((<= 0 b) (div b 2)) ((< b 0) (- (div (- b)
  2))))` stays raw; with `0 < pow(2, n)` (section 6) the sign case goes, then a fold for halving (engine.md 7, A4),
  besides the induction of section 1.

## Order

1. Done in part (Oct 31): sections 3, 5 and 6, 12 tasks correct locally, to be confirmed on the cloud (with the cost
   of the forward lemma `count_length`). Left of section 6: `lasts`, the closed `pow`, the saturating counter (an
   unused second counter among the dependencies, a gap of the matcher), the sums over the same keys (two
   higher-order summands), the constant trace (a pattern on every trace), the bit mask (C).
2. Section 1, after the design decision; it is the largest group by far.
3. Section 4 with the prototype of engine.md 1.2.
4. Sections 2, 7 and the products of section 8, each measured on the cloud.
