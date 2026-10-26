# Changes to the engine of `-prove`

The open changes to the engine, ordered by expected gain; the engine is documented in
[doc/prove.md](../doc/prove.md), the open points of its canonical forms in [canonical.md](canonical.md).

## Plan

### A. Regressions since 0.51.4

The integer counts and the canonical forms (0.52) lost tasks that 0.51.4 solved (cloud, 120 s, one core); the dead
positions (0.52.3: branches and empty combinators dropped, doc/prove.md) and the recursion of `pow` in `-fallback`
are recovered. Open:
- **Timeouts** of array_2-1-simple, array_2-2-simple, linear_sea.ch, nested_4, nested3-1_abstracted, theatreSquare,
  cohendiv, geo1-ll_unwindbound1: measure where the time goes first; the candidate is the renormalization of all
  facts after a merge, which would renormalize only the facts that mention a retired root, by use lists from roots
  to facts as in congruence closure ([canonical.md](canonical.md)).
- **rewnifrev** (true): the goal is left at the array trace with `n == SIZE` known but not substituted into the
  count of `counter`; find the rule that no longer fires (`-debug match,conditions` against 0.51.4).
- The four `_unwindbound1` false tasks (cohencu, ps4, ps5, ps6) are recovered (0.52.4) by the variables of a
  fact that the simplex fixes to a value (`Context.fix`, on the incremental tableau; naturals did it by
  `natural_nonpositive`) and `butlast_counter_consts`. Not done: bound propagation over the rows, which would fix
  variables that the new fact does not mention.

### B. Bounded unrolling for counterexamples and bounded proofs

**Symptom.** Cuvée finds a counterexample only by evaluating a remaining goal of pure arithmetic at small values
(`Eval.counterexample`); a violation after a few iterations of a loop is not found, since the loop is a trace equation
system. On Loops, Korn solves 151 false tasks that Cuvée does not (Cuvée 24 of 209 false), 114 of them the
`_unwindbound` variants of nla-digbench-scaling; on Arrays, the unsafe variants of array-fpi (19) and
reducercommutativity (6 false, 18 true, literal sizes `#define N` of 5 to 60).

**Change.** A transform `-unroll k` on procedures: each loop becomes k nested copies of its body under its test,
followed by
- `assume !test` for counterexamples: a model of the violation of an assertion is a counterexample of the program, if
  the encoding is exact (no abstraction, the arithmetic of C), answered `incorrect`;
- `assert !test` (the unwinding assertion) for proofs: if it and all other assertions hold, the program is explored
  completely, answered `correct`.
Run with growing k (1, 2, 4, 8, ...) within the time limit, by `-vcgen` and z3, before or alongside `-teq` in
`-svcomp`: a `false` answer needs no TEQ, a `true` answer of the unrolling stops the TEQ run. Expected: up to about 120
false tasks on Loops, about 25 on Arrays, plus the `_unwindbound` true tasks with small bounds and the literal sizes
of reducercommutativity.

## 1. Equalities from the simplex to the classes

**Symptom.** `-slice` on `array-crafted/zero_sum1` (fill `a`, add its values to `sum`, subtract them again,
`assert(sum == 0)`): the second loop leaves `sum == sum(prefix(n₂, Tmp?))`, the third subtracts
`sum(prefix(n₃, Tmp?))`, and the assertion holds iff `n₂ == n₃`. The simplex knows `n₂ == SIZE == n₃`, each from two
inequalities (the exit test and the bound of the iteration constraint), but no equation reaches the classes, so the
two sums stay different terms.

**Not a fix: an exchange of all equalities.** Opposite constraints `0 <= p` and `0 <= -p` as equations of the classes,
and the merges of arithmetic terms as equations of the simplex, in rounds: it decided zero_sum1, but every assumed
fact paid for it; on the cloud, Arrays lost 21 results and Loops 13, by timeouts.

**Change.** At the exit of a loop whose counter the test bounds, `!(i < N)` and `i <= N` give `i == N`, stated once
per loop, which the classes solve, so that the counts of two such loops become the same term; or on demand, where
the simplifier compares two atoms of the same function whose arguments differ only in counts. Measure on zero_sum1,
standard_maxInArray_ground and standard_minInArray_ground-2 first.

## 2. Integer reasoning about remainders

**Symptom.** The strided stores (array-tiling `mbpr*`, `pr*`, `pnr*`, 22 true tasks): open is `(i - 1) % 2 == 0`
against `i % 2 == 0` for a variable bound by a combinator. The simplex is rational; the case splits cover remainders
of goal variables only.

**Change.** Remainders by a literal `m` as a fresh variable `r` with `0 <= r < m` and `x == m q + r`, also for bound
variables, with the cases of `r` for small `m`; or `(x + c) % m` normalized to `(x % m + c) % m` with the cases of
`x % m`. Check on mbpr2 first.

## 3. Depth of the case splits

in-de52 and in-de62 have more loops than the four levels of `Prove.cases`; sum_by_3_abstracted stays open at any
depth. Instead of a larger depth: split on the disjunctive premise whose `_cases` rule enables the most rules, or
iterate the depth (2, 4, 8) within the time limit. Not worthwhile: loop unswitching before `-teq` (it doubles the
code with each condition), a disjunctive conclusion moved into the premises.

## 4. Rounds that do not settle

array-crafted bAnd*, bor*, xor*, reducercommutativity avg*, sum* used up the rewrite steps of a goal: the same
instances of forward lemmas are assumed in every round, and the same reads are rewritten in about 31 sibling
contexts. Steps of their own for an instance and a memo of simplified instances did not pay. To be re-measured with
integer counts, which removed the conversion lemmas involved. ps2-ll_unwindbound1 (a timeout at 60 s) belongs here.

## 5. Evaluation of closed instances of the database

Deprioritized (counterexamples are not of interest). 30 unsafe array-fpi tasks remain unknown, e.g. brs2f leaves a sum
over a counter that is false at N = 3, since `Eval.counterexample` evaluates only the functions of `Eval.computed`.
The change would evaluate ground instances of the database by their definitions inside the search for a
counterexample only.

## 6. The join of guarded stores

Cases of an update whose bodies are the same stores up to the stored values merge into one case with conditional
values, as a step of the simplifier ([conditional-stores.md](conditional-stores.md), second variant). It would derive
six lemmas (`stores_cases`, `stores_index_cases`, `select_current_trace_conditional_store(_deps)`, `_cap`,
`_reset_keep`) and cover the 2^s cases of pr3-pr5.

## 7. Matcher limitations with a task behind them

Conditionals inside equations (motivex), the branches of a conditional formula under the facts
(standard_password_ground), rounding and cancellation of factors (count_by_k); each local (TODO.md, "Matching and
rewriting").

## Not in the engine

sum_array-2-2, the recurrences of `ifcomp`, `pcomp`, `sqm-if`, `condm`, the conditional stores of
partial_mod_count_*, and the algorithms not verified under `-teq -prove` are work on the database and the examples
first (TODO.md, "Work queue").
