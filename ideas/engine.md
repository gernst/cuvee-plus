# The engine of `-prove`: open changes, decisions, history

All proposals for the engine of `-prove` in one place (merged on Oct 31, 2026 from prove-next.md, canonical.md,
engine-gaps.md, engine-consolidation.md, dnf-guards.md and nonlinear.md); the open tasks of nla-digbench are in
section 7. The engine is documented in [doc/prove.md](../doc/prove.md), the open tasks and their order in the work
queue of [TODO.md](../TODO.md), the lemma database's side in [database.md](database.md) (its workarounds for gaps of
the engine).

Procedure for a change: change the engine, run the examples of the affected lemmas, the test suite, and one cloud run
of Arrays and Loops against the jar before (`scripts/compare.py`); then replace the workarounds of the database by
their plain forms (Lean proofs by a subagent). The examples of the workarounds (examples/c/teq, examples/dafny/teq) are
the regression tests: they stay `correct`.

## 1. The context and its canonical forms

The context keeps terms in canonical form, Shostak-style (doc/prove.md, "The context"): one order of roots, the
solutions of linear equations in the classes, `Classes.normalize` as the canonizer of `Simplify.var_` and of the facts.
The policy is behind the operations `Classes.term`, `value`, `fixed` and `fact` (0.52.12).

### 1.1 What is substituted

Solutions that are arithmetic over variables, inside arithmetic only. Substituted in every position, they changed the
shapes the lemmas match (the index of a store) and lost half of Arrays. Left-hand sides of rules whose arithmetic is
not canonical (`counter(i, 1, m + 1)`) are matched modulo the classes; which rules no longer match is unchecked.

### 1.2 Normal forms in the context, not in the terms (prototype, not measured)

**Gap.** Under a guard `k == c` with a literal `c`, the class of the iteration variable `k` has the root `c` (a literal
ranks before a variable), and the result is written with `c` instead of `k`; cases that store the same value are no
longer equal (copysome2-1, nr2-nr5: `c[2k := j]`, `c[2k + 1 := 0]` with the literal of the inner `k'`).

**Failed: variables before literals in `Classes.rank`** (0.52.9, reverted in 0.52.10). It lost 30 tasks of Loops, 11
of them "rewriting does not terminate": in benchmark43_conjunctive, `x$16 == n + tmp$7` and `x$16 == 100` solve
`tmp$7` as `-n + 100`, and with `x$16` as the root of the class of `100`, normalization replaces `100` by `x$16`, whose
solution contains `tmp$7` again; `acyclic` does not see it, since a literal has no free variables.

**Design.**
- The context (classes, simplex, facts) keeps literals as roots and normalizes facts completely when they enter it;
  decisions (`eq_`, `implied`, side conditions) are made there, as now.
- Terms are not rewritten with the values of the context: `Simplify.var_` writes a variable as the canonical
  variable of its class (its least variable member), never as a literal; `Simplify.poly` collects summands and folds
  constants without substituting solutions.
- The order of variables prefers the names of the program over fresh names, after the depth of the scope.
- Comparisons in polynomial normal form over the canonical variables; arithmetic as an argument of another function
  (indices, positions of `earlier`) stays as written, its variables canonical.
- The matcher computes the canonical form of an arithmetic argument where a pattern needs it (`a[k]` against
  `a[i - 1]` with `i == k + 1`), memoized by term.

Risks: the cost of the matcher's normalization; places that need literals in terms (`Eval`, literal patterns) get them
only through the matcher; many expected outputs change. The prototype (canonical variables in terms, values inside
arithmetic, the constant of a polynomial as the canonical variable of its class) is kept as a patch; next: measure on
copysome2-1, benchmark43, nr2, then the cloud. copysome2-1 is proved since 0.53.3 by the directed merge of cases
(5.1), so nr2 is the task left behind it.

### 1.3 Ground roots that are no literals

Since 0.53.5 a term whose class has a literal root is written as that literal (`Classes.ground`); a ground term over
constants is not, since it ranks behind the variables. Ranking it before them changes the root of many classes, the
risk of 1.2.

### 1.4 Equalities from the simplex to the classes (set aside until a task needs it)

**Symptom.** zero_sum1 (fill, add, subtract, `sum == 0`): the simplex knows `n₂ == SIZE == n₃` from two inequalities
each, but no equation reaches the classes, so the two sums stay different terms. zero_sum1,
standard_maxInArray_ground and standard_minInArray_ground-2 are solved since 0.52.14 otherwise, and no remaining goal
of the cloud logs (Oct 27) needs it.

**Not a fix:** exchanging all equalities in rounds (opposite constraints as equations, merges as equations of the
simplex) decided zero_sum1 but lost 21 results of Arrays and 13 of Loops, by timeouts.

**Change.** At the exit of a loop whose counter the test bounds, `i == N` once per loop; or on demand, where two atoms
of the same function differ only in counts. Also not done: bound propagation over the rows of the tableau, which would
fix variables that a new fact does not mention (`Context.fix` fixes only those of the new fact).

### 1.5 The cost of canonical forms

- Only the facts that mention a retired root are renormalized (`Classes.retired`), still by a scan of all facts per
  merge; a use list from roots to facts would avoid it.
- The memo of normalized solutions per call of `Classes.normalize` (0.53.23, which cut the cycle of geo1-ll) costs 14
  to 20 % median time. Postponed (Oct 30): entries for solved variables only, no map when no variable is solved, or one
  memo per `Classes` value (tried, no gain: the values are short-lived, a new one at every assumption).

## 2. Arithmetic

### 2.1 Forward instances in the final check (18 geo unwindbound tasks)

The unwindbound variants of geo1-ll, geo2-ll and geo3-ll (6 each) end in `p % 2^64 == 0`, where the forward fact of
`series` (`current_series`) makes `p == 0`; `-debug forward` shows the instance. It exists only in the final check of
the goal (`Simplify.forward`), while `Simplify.mod`, which would take the centered representative of the remainder
(known to be in range in the context) and so write the remainder as `p`, ran before, without the instance. Change:
when the check with the instances fails, simplify the atom once more in the context with the instances. Not a fix: a
rewrite rule `x % m == x` for `0 <= x < m` (tried Oct 31): the argument of the remainder is written with its
coefficients reduced modulo `2^64` (`18446744073709551615 * S + S * z + ...`), only congruent to `p`, so the condition
fails; a forward lemma with a general trigger costs on every task.

### 2.2 Definitions multiplied into products

A closed form of a series over a named geometric sum, `x0 * pow(z, n) + a * geometric(z, n)` (0.53.19), lost
geo1-3_valuebound5 and 10: the arithmetic does not multiply the definition of the value out, so the value times `z` in
the goal is no monomial of the forward fact about the sum. Reverted to the forward fact. The change would substitute
such definitions into products (products of atoms from closed forms, also cohendiv).

### 2.3 Exact division as rational coefficients (cohencu-ll, 7 tasks)

The closed form `x == (3a + 3a²) / 2 + 3 * squares(0, n) + a + 1` with `n == a + 1`; the goal
`10a + 12a² + 6a³ + a⁴ + 3 == (a + 3) * x` is a polynomial identity once the quotients by 2 are exact
(`triangle_even`) and `squares` is its Faulhaber form, but `(a + 3) * x` is a product with a quotient that the linear
arithmetic does not multiply out. Change: a quotient by a literal that is exact in the context as a rational
coefficient (`Arith.Poly` has rational coefficients already).

### 2.4 Division and remainders

- Done (0.52.15): the definition `t == k * (t div k) + t mod k`, `0 <= t mod k < |k|` for a literal `k` when the atom
  enters the arithmetic (`Linear.add`; tcpy, diff-2-n-u); `Simplify.remainders` with definitions constant modulo `n`
  (a general substitution cycles: `x == y + 2`, `y == x - 2`); `(p + c) % m` from a known `p % m` for `m <= 4` and the
  case split on `p % m` (pr2, mbpr2-mbpr4).
- Open: division by a symbolic divisor (mannadiv: `x2 * (n / x2) + n % x2 == n`); `m * (x / m)` as `x - x % m`
  (loopv3, set aside: no divisibility constraints for now); `quot` of C; cancellation (`2 * n / 2`, mlceu2); integer
  rounding (`2 * n <= 2 * k + 1` to `n <= k`, count_by_k).
- Products are not matched modulo commutativity (`m * k` against `k * m`).

### 2.5 One view of arithmetic (done in part, 0.52.13)

`Arith.difference` is the one conversion of comparisons (`Simplify.difference`, `Rewrite.comparison`). Open: the
matcher on `Poly` (its summands the monomials), `Rewrite.sum`/`product` as `Poly.toExpr`, one conversion for `Linear`.
The matcher's signed summands stay for now: they take the expression apart as written, which a polynomial reorders.

## 3. Decisions and derived facts

### 3.1 One decision with a cache

`Simplify.decide` is the decision by the theories (0.52.12); side conditions are decided by simplification at a
positive position (`Rewrite.holds`, 0.53.14) and by lookup among the facts (`Rewrite.known`). Open: a cache per context
(the same pair is decided several times on one path; guard decisions are repeated), and a fixed order of cheap to
expensive checks (syntactic, classes, binders, facts, simplex) behind `eq_`, `holds`, `known` and the helpers. Open
question (Oct 30): polarity and inconsistency are not handled in one principled way; the simplifier still works in
inconsistent contexts, and one case needs it.

### 3.2 Facts derived on assumption

Three mechanisms: `Context.rules` (an equation with a ground term as a rule), forward lemmas (`Forward.assume`,
`saturate`, `Simplify.forward`), `Context.fix` (a variable fixed by the simplex). Proposal: one saturation step of
`Context.assume` with one generation bound. A memo of forward instances keyed by the canonical facts (0.52.13) doubled
the cpu time of Arrays and was removed; forward lemmas fire where the simplifier assumes facts, not in every
`Context.assume`, by decision.

## 4. Matching

### 4.1 Higher-order values at arithmetic arguments (diagnosis open)

With the index in normal form (`-k + m + -1`), `a[-k + m + -1 := F(-k + m + -1)][k := F(k)]` does not match the copy
from both ends, while `a[-k + m + -1 := b[-k + m + -1]]` does (two lemmas `select_current_trace_copy_both_ends(_list)`).
Ruled out: unbound `m` (`-debug match`). Left: the conditions of `Rewrite.abstraction` (`replaced.forall(...)`, the
check against `avoid`).

### 4.2 Keys synthesized from cases (nr2)

The inner loop of two iterations keeps the cases `c[2k := j]` and `c[2k + 1 := 0]`; the shared key `2k + k'` would be
synthesized from the cases (`Rewrite.update`), then `select_current_tiles` applies. Depends on 1.2.

### 4.3 Constants bound by side conditions only (bhmr2007)

`a + b == 3 * n` for two sums whose values add up to 3 needs a lemma whose constant is bound by its side condition
only, which rules do not allow.

### 4.4 Induction on preserved quantities (nla-digbench, about 150 tasks)

A rule on the goal: an atom `P(current(S))` holds if `P` holds of the initial values and every case of the update
preserves it. `P` is the atom abstracted at the current value; the side condition is a polynomial identity per case.
Open: whether such a rule belongs in the database (it is the general rule of loops), which `P` when the goal is not a
single atom over one trace, and components of several accumulators. Analysis in section 7, A1.

### 4.5 Limitations with a task behind them

Conditionals and choices inside comparisons and products (motivex; they are lifted over equations only), the
branches of a conditional formula under the facts (standard_password_ground), rounding and cancellation (count_by_k);
each local. The full list is in TODO.md ("Matching and rewriting", "Trace equation systems").

### 4.6 Matchers as objects (not done, by decision)

The matchers of `Rewrite` take 12 to 15 parameters, most unchanged along a match; a class `Matcher(config, state,
ctx, rule)` and `Simplifier(config, state)` would remove them, but the gain does not outweigh a diff over all of
Simplify and Rewrite.

## 5. Choices and cases

### 5.1 Guards in disjunctive normal form

**Now.** `TEQ.update` groups the paths of a loop body by their results (0.52.11), `Simplify.eps` merges cases with
equal results by the disjunction of their guards, also equal only under the guard of one case (0.53.3, copysome2-1),
and a choice with all results equal is its result. Only equal results merge, by decision (Oct 27): conditional values
lost tasks (database.md, "Conditional stores"). Lifting conditionals out of results (0.52.7) gives
conjunctions, merging reintroduces disjunctions such as `(c && d) || !c`, which the coverage check of the matcher does
not see through (merge, insertion_sort, cocktail_sort).

**Proposal.** Guards are conjunctions of literals, disjoint (a test `a || b` becomes the cases `a` and `!a && b`);
cases with equal results stay apart, except a choice whose results are all equal; each result is simplified under its
own conjunction. The matcher needs no change for concrete pattern guards (the direction is from the expression to the
pattern). For a higher-order guard variable (`case C(k) => a[k := V(k)] case !C(k) => a`), the matcher groups the
expression cases whose results match under the same instantiation and binds `C` to the disjunction of their guards;
the complementary case covers the rest. That is the merging of `Simplify.eps`, on demand.

**Risks.** DNF is exponential in sequenced conditionals, as `-teq` already is (bugs.md); lemmas written against
merged guards (`bisection`) are to be checked (`scripts/missing.py`).

**Steps.** Drop the merging of `Simplify.eps` and `TEQ.update` except for all-equal results; split disjunctive tests;
the grouping in `Rewrite`; rerun and compare.

### 5.2 The join of guarded stores

Cases whose bodies are the same stores up to the stored values merge into one case with conditional values, as a
local step of the simplifier on `Eps`, iterated by the outer loop (database.md, "Conditional stores"). It would derive
`stores_cases`, `select_current_trace_cap` and `select_current_trace_reset_keep`, and cover mods and modsf (strided
stores without a fixed number of cases); the others of that kind are taken by the folds `stores_where` and
`strides₂` to `strides₅` since Oct 28. In tension with the decision of 5.1; measured once: pr3 proved, rew and ms2
lost.

### 5.3 Depth of the case splits

in-de52 and in-de62 have more loops than the four levels of `Prove.cases`; sum_by_3_abstracted stays open at any
depth; mbpr4 needs the case `i == 2` of `0 < i < 3` after the choices are lifted out of an atom. Instead of a larger
depth: split on the disjunctive premise whose `_cases` rule enables the most rules, or iterate the depth (2, 4, 8).
Not worthwhile: loop unswitching before `-teq` (doubles the code per condition).

### 5.4 One module of choices (not done, by decision)

Cases are built, lifted, merged and split in `TEQ.update`, `Simplify.eps`, `Simplify.cases`, `Normalize.lift`,
`Prove.cases`, and sequents are decomposed three times (`Split`, `Normalize.flatten`, `Context.assume`). They do
different things; they stay.

## 6. Search, termination, speed

### 6.1 Rounds that do not settle

With 15 min, 116 tasks end at the bound of the rewrite steps (103 of Loops, 13 of Arrays), e.g. fermat1, egcd2,
mannadiv: the same forward instances are assumed in every round, the same reads rewritten in about 31 sibling contexts.
Steps of their own per instance and a memo of instances did not pay; `-prove:steps 10000` gains little. A larger target
than speed.

### 6.2 Speed

Profile (Java Flight Recorder, 15 s per task, 0.52.8; linear_sea.ch, theatreSquare, array_2-2-simple, rewnifrev):
matching 30 to 65 %, half of it the side conditions of rules; `Forward.saturate` 13 to 22 % in two of four; the simplex
17 to 20 %; `Context.fix` 6 to 17 %; `Poly.normalize` 14 to 26 %; hashes of terms 6 to 19 %, recomputed recursively at
each lookup; loading the database 4 to 8 %. The structural ordering of `Expr` (0.52.6) gained 10 to 20 %. Candidates,
cheapest first: a cached hash per term, a memo of the decided conditions per context, `Context.fix` only for a variable
bounded from both sides, an incremental tableau per context. Constant factors: they move tasks at the limit (string-1,
divbin(2)_unwindbound1, add-2-n-u, cohendiv-ll_valuebound2, nested3-1_abstracted), not the regressions.

### 6.3 Bounded unrolling for counterexamples and bounded proofs

Counterexamples come only from evaluating a remaining goal of pure arithmetic (`Eval.counterexample`). Korn solves
151 false tasks of Loops that Cuvée does not, 114 of them `_unwindbound` variants; on Arrays the unsafe array-fpi and
reducercommutativity with literal sizes. Change: `-unroll k`, each loop k nested copies of its body, then
`assume !test` (a model is a counterexample if the encoding is exact: `incorrect`) or `assert !test` (the unwinding
assertion: `correct`), by `-vcgen` and z3, with growing k, before or alongside `-teq`. Expected: up to about 120
false tasks of Loops and 25 of Arrays. Also a method of the portfolio ([doc/benchmarks.md](../doc/benchmarks.md),
"The portfolio").

### 6.4 Evaluation of closed instances

Deprioritized. 30 unsafe array-fpi tasks stay unknown (brs2f: a sum over a counter, false at N = 3), since
`Eval.counterexample` evaluates only `Eval.computed`; ground instances of the database would be evaluated by their
definitions inside the search for a counterexample only.

## 7. Nonlinear loops (nla-digbench)

The open tasks of nla-digbench and nla-digbench-scaling with the verdict true, by the concept they need. Started on
Oct 29, 2026 from the cloud run of 0.53.14 without fallback (`-svcomp -rules`): 221 open tasks of 24 programs, 46 of
them `unknown` with a residual goal in the log, 175 timeouts, whose loops were read from the sources. State of Oct 31
(0.53.23, cloud at 120 s and 300 s). The gaps of the engine behind the arithmetic are in section 2.

### Done

- **Wrap-around modulo 2^64 of affine updates** (geo1-3): reduction modulo `M` commutes with the ring operations,
  so `current(trace(x0, ... :: (x * A + B) % M))` is the value without the remainder, modulo `M`
  (`current_trace_mod_affine`, `current_trace_mod_mul`, unsigned.dfy; `current_trace_mod_affine_wrapped` for an
  initial value wrapped from `int`, geo3-ll). The fold `series` and `current_trace_geometric` then apply, with the
  forward fact `current_series` `(z - 1) * current(series(x0, z, a, n)) + a == ((z - 1) * x0 + a) * pow(z, n)` and the
  values for no and one iteration (`current_series_zero`, `current_series_one`, `pow_zero`, `pow_one`). geo2-ll,
  geo3-ll, the valuebound variants, geo1-ll (since the memo of solutions, 0.53.23, cut a cycle of the classes) proved.
- **A trace that does not read its accumulator** (cohendiv-ll): `current_trace_last` (counters.dfy), the update at
  the last iteration; `current_trace_constant` is its case of a constant update.

### Open, in the database

#### A1. Quantities that every case preserves (most of the family, about 150 tasks)

The asserted equations of dijkstra, knuth, egcd, egcd2, egcd3, lcm1, lcm2, fermat1, fermat2, divbin, divbin2, hard,
prod4br, prodbin, bresenham, cohendiv are polynomial invariants that each case of the update keeps: egcd
(`a > b ? (a -= b, p -= q, r -= s) : (b -= a, q -= p, s -= r)`) keeps `a == p*x + r*y` and `b == q*x + s*y`, fermat2
keeps `4*(A + r) == u*u - v*v - 2*u + 2*v`, prod4br `q + a*b*p == x*y`. These loops have no closed form (a guard
compares accumulators), and the goal does not need one.

The principle is induction as a rule on the goal: `P(current(S))` holds if `P` holds of the initial values and every
case preserves it, `invs(for deps check x, ... :: P(x) ==> P(update(x)))`, `P` the atom abstracted at the current
value. Several equations that only hold together (egcd's two) need their conjunction as `P`. The side condition is a
polynomial identity per case. Open: whether such a rule belongs in the database (it is the general rule of loops,
which the trace equations otherwise replace by closed forms), which `P` when the goal is not a single atom over one
trace, and the components of traces of several accumulators (4.4).

#### A4. Doubling with a literal factor (cohendiv, hard, divbin, divbin2, prodbin, dijkstra)

`a = 2 * a` stays raw (`trace(1, ... :: (* 2 v0))`): `current_trace_geometric` has the pattern `y * z`, and the
product with the literal first does not bind the accumulator. To check: a variant `z * y`, or the matcher of products
(2.4). The halving loops (`b = b / 2`, `q = q / 4`) are the inverse, which needs division by powers.

#### A5. Increments chosen by a guard on the accumulator (bresenham, fermat2, mannadiv)

bresenham: `v < 0 ? v += 2Y : (v += 2Y - 2X, y++)`; the guard reads `v`, so `sums` does not fold `v`, while `y`
counts the second case. A value with a constant increment per case is its initial value plus the increments counted
by case, `v == v0 + 2Y n - 2X y`. mannadiv's reset counter (`y + 1 == c ? 0 : y + 1`) is the counter modulo `c`
(`mods` of teq:unsigned), if the initial value is below `c`; mannadiv then needs division by a symbolic divisor
(2.4).

#### A6. Binary expansion (prodbin, prod4br, divbin, divbin2, hard, dijkstra)

`y = y / 2` by the parity of `y`, `z += x` for odd `y`: `z` is `a` times the bits of `b` seen so far. Closed forms need
division by powers in the arithmetic; A1 is the simpler route (the asserted invariant `z + x*y == a*b` is preserved by
both cases).

### Open, elsewhere

- **The unwindbound variants of geo1-ll, geo2-ll, geo3-ll** (18 tasks): `p % 2^64 == 0` with `p == 0` by the forward
  fact of `series`, which exists only in the final check (2.1).
- **geo1-3 valuebound5 and 10 with a closed form**: proved with the forward fact; a closed form over `geometric`
  needs definitions multiplied into products (2.2).
- **cohencu-ll** (7 tasks): exact division by 2 in polynomials (2.3).
- **A7. Trace systems that explode** (egcd2-ll, egcd3-ll, fermat1-ll, lcm1, about 40 tasks): nested loops whose `-teq`
  output has 3120 to 23664 traces (3 to 48 for the others) time out before any lemma matters; a question of
  `TEQ.system` for nested loops of several accumulators.
- **Expected false**: the geo1-u variants and hard-ll_unwindbound1 among the unknown tasks of Oct 31.
- **Floating point** (freire1, 7 tasks): uninterpreted sorts of floats; out of scope.

### Order, by tasks per concept

1. A1, the general rule: most of the remaining tasks, after a design decision (above).
2. The final check with forward instances (2.1): 18 tasks, one change of the engine.
3. A4 and A5, small lemmas, then A6 if A1 is not taken.
4. Exact division (2.3), cohencu.
5. A7, the size of the trace systems of nested loops, in TEQ.

## 8. Not done, and why

- **Instantiating iteration constraints at reads** (assume_abort.c, standard_sentinel-2): quantifier instantiation,
  which the design avoids; an iteration constraint is never a side condition, since deciding it builds the contexts
  of the `invs` facts, whose reads match again. Rules on the atoms instead.
- **Terms with binders modulo bound names in the classes** (sumt2): re-keying binder nodes on every merge; the
  workaround of `compacts` and `filters_*` stays.
- **Sums in patterns** (the empty sum, several summands, literal coefficients): restricted on purpose, against loops
  such as `x + 1` matching `1` with `x = 0`; `maps_counter_scale`, `select_current_trace_prefix_sums_add`,
  `select_current_trace_ahead_down`, `mul_lt_cancel` stay.
- **Forward lemmas for division and parity** (`div_mod`, `mod2_succ`): triggers at every division; 2.4 instead.
- **A memo of forward instances** (0.52.13): see 3.2.
- **`haslength(n, xs)`** dropped when `xs` occurs nowhere else (functions_1-2): one task, a special case for one
  function of the database.
- **Variables before literals as roots** (0.52.9): see 1.2.
- **Matchers as objects, one module of choices**: 4.6, 5.4.

## 9. Design notes

What the work on the regressions of the integer counts showed (Oct 26, 2026):
- Unreachability is a property of the context that the traversal builds for each position anyway (branches, cases,
  bodies of combinators); it decides there, not by a rule of its own.
- A term is simplified or removed, never left as it is: rules match shapes, and a frozen term blocks them elsewhere
  (the beta-redex of an empty map in eqn3f).
- Termination comes from the rules (structural patterns, definitions by match as rules), not from where the engine
  stops; a conditional rule that terminates only because its condition fails is fragile (swap.dfy).
- Closed instances are evaluated, not rewritten: naturals unfolded `succ(zero)` for free, integers need `Eval`.
- The theories exchange what they know, as Nelson-Oppen does: the simplex fixes variables that the classes need,
  for the variables of a new fact, model-based on the incremental tableau.
- Canonical forms need incremental bookkeeping: only the facts that mention a retired root are renormalized.
- Most problems of the canonical forms were at the seams between mechanisms that do the same in different places
  (the review of Oct 26): hence one policy for normal forms, one view of arithmetic, one decision, one memo table.

## 10. History

- **Regressions since 0.51.4** (cloud, 120 s, Oct 26): rewnifrev (recovered in 0.53.14), linear_sea.ch, geo1 (geo1-ll
  correct since 0.53.23), prodbin-ll, cohendiv-ll (fallback), max20-1; 6 to 71 rewrite steps in 15 s each, the time in
  the engine around the rewriting (6.2). Open ones: TODO.md.
- **Losses of Oct 28** (0.52.16 to 0.53.13): brs2-brs5, ps2-ps6_valuebound1, pr3, pr4, pr5 recovered by lemmas or the
  lifting with complete guards (0.53.10); nested_4 since 0.53.10; mods, modsf only with the withdrawn merge of
  conditional stores; sep, cohencu lost with fallback (the goals that reach z3 changed with the multisets).
- **Done:** comparisons of conditionals with literals in `eq_` (0.52.9); failed matches of all rules in `-debug match`
  (0.52.9); paths grouped by results in `TEQ.update` (0.52.11); the policy of normal forms behind four operations of
  `Classes`, `Simplify.decide`, `Normalize.replace` with `binders`, `Rewrite.counter` (0.52.12); `Arith.difference`,
  `Rewrite.alternatives` (the definitions, the structural and the projected view), `Context.memo` for combinators and
  reads (0.52.13); `Views.self`, `Simplify.update`, `view`, `leaf`, `Rewrite.front` (Oct 27); remainders and division
  (0.52.15); the directed merge of cases (0.53.3); side conditions at a positive position, `ite` of equal branches,
  equations with terms of one sign on the left (0.53.14); the memo of normalized solutions (0.53.23).
