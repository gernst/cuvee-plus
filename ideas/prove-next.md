# Changes to the engine of `-prove`

The open changes to the engine, ordered by expected gain; the engine is documented in
[doc/prove.md](../doc/prove.md), the open points of its canonical forms in [canonical.md](canonical.md).

## Plan

### A. Unreachable positions are `undefined`

**Symptom.** Since 0.52.2 an expression in an inconsistent context stays as it is (`Simplify.simplify`), which ends
the rewriting without end in dead branches (swap.dfy), but leaves their terms in the goals: on the cloud (120 s, one
core, against 0.52.1 with the canonical forms), four counterexamples of array-fpi (eqn3f, eqn4f, nsqmf, sqmf) become
unknown, with `-fallback` a solver error; SV-LIB CTranslated loses five true tasks (afnp2014, benchmark01, 22, 40, 53
of loop-zilu, benchmark01 by "rewriting does not terminate"); Loops loses nested3-2_abstracted (false) and
sum_by_3_abstracted (true).

**Change.** An expression at an unreachable position has no meaning, so any value is right there; the value is
`undefined`, of the type of the expression, rather than the expression:
1. A constant `undefined` of the core, polymorphic in its type (`Fun.undefined`, sugar `Undefined(typ)`), independent
   of the TEQ declarations; `unspecified` of teq.dfy (the value of an update where no guard holds) stays, since its
   meaning differs: some value of the type, the same one at each occurrence of the trace.
2. `Simplify.simplify`: in an inconsistent context, a formula is decided by its polarity as now, any other expression
   is `undefined`; a formula at a neutral position as well (it has no polarity to decide it).
3. `Simplify.ite`: a branch whose context is inconsistent gives the other branch, `ite(c, a, b)` is `b` if the context
   with `c` is inconsistent, also when `c` itself is not decided; likewise for the cases of `Eps` and of `match`, a
   case whose guard contradicts the context is dropped.
4. `undefined` absorbs nothing else: `f(undefined)` stays, an equation with it is not decided; it occurs only where
   the position is unreachable, so it must not reach a goal at a reachable position. Check: no goal output of the
   examples contains it; `-fallback` and the printers lower it to a fresh constant of its type per occurrence (sound:
   an arbitrary value), and `Eval` treats it as no value (no counterexample through it).

Check on eqn3f, benchmark22 of loop-zilu (SV-LIB) and swap.dfy first, then the 94 examples and the cloud.

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
