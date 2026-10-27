# Changes to the engine of `-prove`

The open changes to the engine, ordered by expected gain; the engine is documented in
[doc/prove.md](../doc/prove.md), the open points of its canonical forms in [canonical.md](canonical.md).

## Plan

### A. Regressions since 0.51.4

The integer counts and the canonical forms (0.52) lost tasks that 0.51.4 solved (cloud, 120 s, one core); the dead
positions (0.52.3: branches and empty combinators dropped, doc/prove.md) and the recursion of `pow` in `-fallback`
are recovered. Open, against 0.51.4 (Oct 26, 2026, 0.52.4 at 120 s, checked at 15 min with 0.52.5):

| Task | 0.51.4 | now (15 min) | most frequent rewrites in 15 s (local, 0.52.5) |
|---|---|---|---|
| rewnifrev (Arrays, MonoCera) | true 17 s | unknown, timeout | `earlier(k, ⌊I⌋)` 22 of 29: the same read of the counter `i` at many positions |
| linear_sea.ch | true 25 s | timeout | `uint((tmp div 2) + 1)`, `quot(tmp, 2)`: unsigned arithmetic with division (binary search) |
| geo1-ll_unwindbound1 (fallback) | true 66 s | step bound | `ulonglong(k)`, `ulonglong(c + 1)` 15 each: wrapping of unsigned long long |
| prodbin-ll_valuebound5, 50, 100 (fallback) | true 41–77 s | timeout | `rem(y, 2)`, `quot(y, 2)`: C's division of the halving loop |
| cohendiv-ll (fallback) | true 116 s | timeout | `current(trace(b…))` with `pow` |
| max20-1 (fallback, Arrays) | true 82 s | timeout | reads of the array trace |

Work again (cloud, Oct 26, 2026, 0.52.4 with the database of that day, 120 s, ideas/array-lemmas.md): array_2-1-simple
(false, 26 s) and array_2-2-simple (28 s), without any of the new rules, presumably by the removal of
`store_occurs_selects`, whose instances came back at every read of a store; theatreSquare with the fallback (61 s).
sum_by_3, sum_by_3_abstracted and sum_array-2-2 (TODO.md, "Lost tasks") are solved by 0.52.4 itself.

Only slower, solved within 15 min: nested_4 (107 s), nested3-1_abstracted (129 s), cohendiv-ll_valuebound10 (75 s),
prodbin-ll_valuebound20 (101 s).

None of them rewrites without end: 6 to 71 rewrite steps in 15 s. The time goes into the engine around the rewriting;
stack samples of array_2-1-simple show three places:
- the matcher on comparisons: `Rewrite.comparison` normalizes a polynomial for each rule it tries on a comparison, and
  `Poly.normalize` sorts its monomials by the ordering of `Expr`, which compares the terms printed as strings
  (`Ordering.by(_.toString)`, Expr.scala); old, but the canonical forms normalize far more often;
- forward lemmas: `Forward.saturate` looks up facts by `Rewrite.known` and `Classes.equal`, hashing deep terms;
- the checks of `Context.implied`, through `Classes.add`.
The structural ordering of `Expr` (0.52.6) made the engine 10 to 20 % faster and gained about ten tasks near the
limit, none of the regressions above (array_2-1-simple came back with the database, see above). A profile (Java Flight
Recorder, 15 s per task, 0.52.8, shares of the samples) of linear_sea.ch, theatreSquare, array_2-2-simple, rewnifrev:
- matching 30 to 65 %, of which the side conditions of rules (`Rewrite.conditions`, each a check of `denied` or
  `implied` through the simplex) about half in linear_sea.ch and array_2-2-simple;
- `Forward.saturate` 13 to 22 % in two of the four, not the main cost;
- the simplex 17 to 20 %; `Context.fix` 6 to 17 %; `Poly.normalize` 14 to 26 %; renormalization 14 % in theatreSquare;
- the hashes of terms 6 to 19 % on their own (`hashCode` of `Sort`, `Con`, `Var`, `Type`), recomputed recursively at
  each lookup in a map; loading the database 4 to 8 %.
Candidates, cheapest first: a cached hash per term, a memo of the decided conditions of rules per context, `Context.fix`
only for a variable that a fact bounds from both sides.

Perhaps not worthwhile: these are constant factors, while the tasks above mostly do not finish with more time either
(15 min solve few of them, and 116 tasks end at the bound of the rewrite steps, see below); a speedup moves the tasks
just at the limit, as the ordering did, not the regressions. The repeated reads (rewnifrev), the unsigned arithmetic with
division (linear_sea.ch, geo1, prodbin), whose wrapping functions and `quot`/`rem` the database and the canonical forms
treat as atoms, and the rounds that do not settle (item 4) are where the tasks are.
- The four `_unwindbound1` false tasks (cohencu, ps4, ps5, ps6) are recovered (0.52.4) by the variables of a
  fact that the simplex fixes to a value (`Context.fix`, on the incremental tableau; naturals did it by
  `natural_nonpositive`) and `butlast_counter_consts`. Not done: bound propagation over the rows, which would fix
  variables that the new fact does not mention.

More time (cloud, cuvee-fallback, 0.52.5, 15 min and two cores against 120 s and one core, Oct 26, 2026): Arrays
160/62 to 162/62, Loops 252/29 to 294/30, no losses; the gains are nla-digbench (cohendiv, divbin, egcd, fermat2,
lcm2, prod4br, after 100 to 700 s) and a few others (apache-get-tag, bh2017-ex-add, nested_4, nested3-1_abstracted).
The tasks that time out at 120 s mostly do not finish: with 15 min, 103 of Loops and 13 of Arrays end at the bound of
the rewrite steps ("rewriting does not terminate"), i.e. their rounds do not settle (item 4), which is the larger
target than their speed.

### A2. Tasks lost since 0.52.4 (Oct 28, 2026)

The tasks that at least one of the runs of Oct 26 to 28 solved (the runs of the comparison of TODO.md; "last solved
by" in their order), but ffb2ad81 (0.52.16 with teq:multisets, cloud, Ryzen, 120 s, one core) did not. The column "0.52.17"
is the run of fa09ee89 under the same configuration.

| Task | Verdict | Last solved by | Time there | 0.52.17 |
|---|---|---|---|---|
| array-fpi/brs2 | true | 0.52.4 | 24 s | recovered |
| array-fpi/brs3 | true | 0.52.4 | 25 s | recovered |
| array-fpi/brs4 | true | 0.52.4 | 26 s | recovered |
| array-fpi/brs5 | true | 0.52.4 | 28 s | recovered |
| array-tiling/pr3 | true | the merge of conditional stores (withdrawn) | 40 s | recovered |
| nla-digbench-scaling/ps2-ll_valuebound1 | true | 0.52.8 | 17 s | recovered |
| nla-digbench-scaling/ps3-ll_valuebound1 | true | 0.52.8 | 23 s | recovered |
| nla-digbench-scaling/ps4-ll_valuebound1 | true | 0.52.8 | 26 s | recovered |
| nla-digbench-scaling/ps5-ll_valuebound1 | true | 0.52.8 | 34 s | recovered |
| nla-digbench-scaling/ps6-ll_valuebound1 | true | 0.52.8 | 39 s | recovered |
| array-fpi/mods | true | the merge of conditional stores (withdrawn) | 21 s | unknown |
| array-fpi/modsf | false | the merge of conditional stores (withdrawn) | 22 s | unknown |
| array-multidimensional/diff-2-n-u | true | 0.52.15 | 93 s | timeout |
| loop-acceleration/functions_1-2 | false | the choices as arrays (branch) | 16 s | unknown |
| loop-simple/nested_4 | true | 0.52.16 | 112 s | timeout |
| loops-crafted-1/nested3-1_abstracted | true | 0.52.13 without the forward memo | 106 s | timeout |
| nla-digbench-scaling/divbin2_unwindbound1 | true | the conversion of all folds to multisets | 103 s | timeout |
| nla-digbench-scaling/divbin_unwindbound1 | true | the conversion of all folds to multisets | 103 s | timeout |

New in 0.52.17, not lost before: array-tiling/pnr2, nla-digbench-scaling/cohencu_valuebound1; array-tiling/pr4 and
pr5 are true locally in 88 s and on the cloud in 485 s (15 min).

- Recovered in 0.52.17: brs2-brs5 (the lifting of conditionals into cases of 0.52.7 split the addition of the
  reset-add loop; `select_current_trace_reset_add_keep`), the valuebound1 variants of ps2-ps6 (a residue of higher
  degree in a variable of two values; `square_eq_self` and the case split on two-element intervals), pr3 (its shape
  lemma, strided stores step 3).
- Left, at the limit (93 to 112 s when solved, alternating between runs): diff-2-n-u, nested_4,
  nested3-1_abstracted, divbin, divbin2; they need speed, not lemmas.
- Left, only with the withdrawn merge of conditional stores: mods, modsf (strided stores, step 3, without a fixed
  number of cases).
- Left, lost with the lengths of the lists of choices (0.52.16): functions_1-2 (a list of a given length must exist);
  z3 does not show that either, left as it is.

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

Sections 1 and 2 are current work (TODO.md, "Work queue: Now"), before plans A and B.

## 1. Equalities from the simplex to the classes (set aside, Oct 27)

zero_sum1, standard_maxInArray_ground and standard_minInArray_ground-2 are solved by 0.52.14, and no remaining goal of
the cloud logs of Arrays and Loops compares counts that only the simplex knows equal; set aside until a task shows up.

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

## 2. Integer reasoning about remainders (done in part, 0.52.15)

Done: `(p + c) % m` from a known `p % m` for `m <= 4` (`Simplify.mod`) and the case split on `p % m` (`Prove.remainders`),
with the definition of div and mod in the simplex: pr2, mbpr2-mbpr4. Open: pr3-pr5 and pnr*, whose updates have 2^s cases
(ideas/conditional-stores.md).


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

## Design notes

What the work on the regressions of the integer counts showed (Oct 26, 2026):
- Unreachability is a property of the context that the traversal builds for each position anyway (branches, cases,
  bodies of combinators); it decides there, not by a rule of its own.
- A term is simplified or removed, never left as it is: rules match shapes, and a frozen term blocks them elsewhere (the
  beta-redex of an empty map in eqn3f).
- Termination comes from the rules (structural patterns, the definitions by match as rules), not from where the
  engine stops; a conditional rule that terminates only because its condition fails is fragile (swap.dfy).
- Closed instances are evaluated, not rewritten: naturals unfolded `succ(zero)` for free, integers need `Eval`.
- The theories exchange what they know: the simplex fixes variables that the classes need (the `_unwindbound1` tasks),
  as Nelson-Oppen exchanges implied equalities; done for the variables of a new fact, model-based on the incremental
  tableau, not by bound propagation over the rows.
- Canonical forms need incremental bookkeeping: only the facts that mention a retired root are renormalized.

## Not in the engine

sum_array-2-2, the recurrences of `ifcomp`, `pcomp`, `sqm-if`, `condm`, the conditional stores of
partial_mod_count_*, and the algorithms not verified under `-teq -prove` are work on the database and the examples
first (TODO.md, "Work queue").
