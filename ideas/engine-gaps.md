# The gaps of the engine behind the workarounds of the database

A plan (Oct 26, 2026) to close the gaps of `-prove` for which the database has workarounds, such that the lemmas can be
stated in their plain forms. The workarounds are listed in [database-review.md](database-review.md) ("Workarounds for
gaps of the engine") and [array-lemmas.md](array-lemmas.md). The examples of the workarounds (examples/c/teq,
examples/dafny/teq) are the regression tests: after a workaround is replaced by its plain form they stay `correct`,
their `_wrong` variants `unknown`.

Procedure per step: change the engine (in a worktree, without the uncommitted changes of other sessions), run the
examples of the affected lemmas, the test suite, and one cloud run of Arrays and Loops (out/bench/cuvee-arrays.xml,
the jar of main against the new one, `scripts/compare.py`); then replace the workarounds by their plain forms (Lean
proofs by a subagent).

## 1. Comparisons of conditionals with literals (done, 0.52.9)

**Gap.** `assume_abort_if_not(c)` of C reaches the goals as `ite(c, 1, 0) != 0`, which `Simplify.eq_` does not reduce
to `c`: it has no case for a conditional against a literal. Inside `invs` the constraint stays in that form, so no rule
on `c` matches (array_init_nondet_vars, array_init_pair_symmetr2).

**Change.** In `Simplify.eq_`, a case `(Ite(test, a, b), d)` with literals `a`, `b`, `d` (and the mirrored one) is
`ite(test, eq_(a, d), eq_(b, d))`; the helper `ite` makes `ite(c, true, false)` the test and `ite(c, false, true)` its
negation. Local to `eq_`, no new terms.

**Tests.** examples/c/teq/assume_abort.c: the constraints are `0 < tmp` and `tmp < 10`; its goal remains, since the
constraint is not instantiated at the position read (see "Not done"); the same holds for array_init_nondet_vars and
array_init_pair_symmetr2, which need a rule on the atom of their goal in addition.

## 2. Failed matches of all rules in `-debug match` (done, 0.52.9)

**Gap.** `-debug match` reports failed matches only for rules on traces; for others (e.g. a comparison whose side is
a read of a trace) nothing is printed, which makes failures such as the higher-order value of the copy from both ends
hard to diagnose.

**Change.** In `Rewrite`, a line for every rule whose left-hand side has the head of the term (the function of an
application, the kind of a combinator) but does not match, only with `-debug match`; and a line for an argument of a
higher-order variable whose variables are not bound yet. The first subterm that fails is not reported yet.

## 3. Variables kept instead of literals (0.52.9, failed and reverted in 0.52.10; see 3b)

**Gap.** Under a guard `k == c` with a literal `c`, the class of the iteration variable `k` has the root `c`
(`Classes.rank`: a literal before a variable), and `Classes.normalize` writes the result with `c` instead of `k`. Two
cases that store the same value are then no longer equal: in copysome2-1, `if (i != z) a3[i] = a2[i]; else a3[i] =
a1[i];` (with `a2[i] == a1[i]` for `i != z`) becomes

```
case k != 150000 => a[k := earlier(k, T)]
case k == 150000 => a[150000 := earlier(150000, T)]
```

which `Simplify.eps` does not merge, so the fold `stores` does not apply; the database has `stores_cases_point`.

**Change.** In `Classes.rank` (the order given by `Context.order`), every variable comes before literals. Only the
variables of combinators would do, but no total order has a local variable before a literal, a literal before an
outer variable, and an outer variable before a local one (the canonical forms write inner variables by outer ones).
`Context.fix` recognized a variable fixed by the simplex by a literal root and assumed its value again without end; it
looks for a literal among the members now. The literal stays in the class and the simplex knows `k = c`, so comparisons
and reads over stores are decided as before; the existing merging of `Simplify.eps` then combines the two cases into
`a[k := earlier(k, T)]`. Lemmas whose patterns use the literal (`select_current_trace_recurrence`, `case i == 0 =>
a[0 := c]`) still match, since the matcher follows the members of a variable's class.

**Risk.** Terms that are evaluated only with the literal: arithmetic stays `k + 1` instead of `1` (the simplex decides
it alike), but closed instances for `Eval` and reads such as `earlier(k - 1, ...)` at `k == 0` keep `k`. The
experiment measures it: the test suite and the cloud run, before any change of the database.

**Database.** `stores_cases_point` (arrays.dfy) goes, `trace_merge_cases_ne` (counters.dfy) presumably too.

**Tests.** examples/c/teq/stores_cases_point.c is correct without the lemma (local, Oct 26; unknown with 0.52.8 within
10 s); copysome2-1, the users of `trace_merge_cases_ne`. The lemma stays until the cloud run of Arrays and Loops shows
the cost of the change (out/bench/cuvee-arrays.xml, tool-main against tool-rank).

## 3b. Normal forms in the context, not in the terms (redesign of step 3)

**Result of step 3 (0.52.9).** Variables as roots before literals lost 30 tasks of Loops in the cloud (11 of them
"rewriting does not terminate"), Arrays even. The cause, traced on loop-zilu/benchmark43_conjunctive: `x$16`, the
value of `x` at the exit, is solved as `n + tmp$7`, the exit gives `x$16 == 100`, so `tmp$7` is solved as
`-n + 100`; with `x$16` as the root of the class of `100`, `Classes.normalize` replaces the literal `100` in that
solution by `x$16`, whose solution contains `tmp$7` again, without end (432551 levels, then a stack overflow, which
Simplify reports as "rewriting does not terminate"); `acyclic` does not see it, since a literal has no free variables.
A literal was canonical only because it was always its own root.

**Design.**
- The context (classes, simplex, facts) keeps literals as roots (the order before 0.52.9) and normalizes facts
  completely when they enter it (`Context.assume`, `Context.renormalize`): solutions, roots, literals. Decisions
  (`eq_`, `implied`, side conditions) are made there, as now.
- Terms are not rewritten with the values of the context: `Simplify.var_` replaces a variable by the canonical
  variable of its class (its least variable member), never by a literal; `Simplify.poly` builds the polynomial without
  substituting solutions (`Classes.substitute`), but still collects summands and folds constants.
- The order of variables prefers those without an index (the names of the program) over those with one (fresh names,
  the variables of binders), after the depth of the scope, so that inner variables are still written by outer ones.
- Equations and inequalities of arithmetic are presented in polynomial normal form (`Simplify.le`, `lt`, `poly.sides`)
  over the canonical variables, without solutions; arithmetic as an argument of another function (the index of a read
  or store, the position of `earlier`, arguments of uninterpreted functions) stays as written, its variables canonical.
- The matcher computes the canonical form of an arithmetic argument from the context where a pattern needs it (a
  pattern `a[k]` against `a[i - 1]` with `i == k + 1`), memoized by term; since variables are canonical already, only
  the arithmetic around them is normalized, not the chains of the classes at every variable.

**Expected.** The result of a case `k == c` keeps `k` and is merged with the other cases of the same result
(copysome2-1 without `stores_cases_point`); no literal becomes a variable or a variable a literal inside a term; goals
keep the names of the program. Risks: the cost of the matcher's normalization; places that need literals in terms
(`Eval`, rules with literal patterns) get them only through the matcher; the expected outputs of many examples
change (regenerated only once the measurement says the design pays off).

**Steps.** (1) Main back to literal roots: `Classes.rank` and `Context.fix` of 0.52.9 reverted, steps 1 and 2 kept
(done, 0.52.10). (2) Prototype in a worktree: `var_`, `poly`, the order of variables, the matcher. (3) Measure: the
examples of the lemmas of Oct 26, copysome2-1 without `stores_cases_point`, benchmark43 (10 s each), then the cloud
run of Arrays and Loops against 0.52.10.

## 3c. Merging cases (Oct 26)

- Done (0.52.11): the cases of the paths of a loop body are grouped by their results in `TEQ.update`, before any
  simplification; examples/c/teq/stores_cases_point.c (two branches storing `a[i]`) is proved without the lemma.
  copysome2-1 is not: its branches store `a2[i]` and `a1[i]`, equal only by the earlier loop.
- A single guarded case stays a choice in `TEQ.update` (0.52.12): dropping its guard, as `Simplify.eps` does under the
  iteration constraint, changed the output of examples/dafny/teq/fallback.dfy (`-teq -fallback`, no simplifier): the
  conjunct `a[I(j)] != 0` of the iteration constraint and the exit value `i == I(n)` were missing, although the
  constraint is built from the paths, not from the updates; which part of TEQ or `-fallback` uses the guard of the
  update is open.
- Rejected: merging in `Simplify.eps` by assuming the guards. Both guards are false together (disjoint), the
  disjunction is too weak (the results differ under the other guard).
- Done (0.53.3): the directed test, `e₁` equal to `e₂` under the guard of the case of `e₂` (then `e₁` covers both),
  and the converse, for guards with an equation; it merges copysome2-1 (doc/prove.md, "Cases with equal results").
- The prototype of 3b (canonical variables in terms, values inside arithmetic, the constant of a polynomial written
  as the canonical variable of its class) is kept as a patch, not measured in the cloud; ideas/engine-consolidation.md
  proposes to put the policy of normal forms into one place first.

## 4. Remainders and division (done, Oct 27, 0.52.15)

**Gaps.** (a) `Simplify.remainders` substitutes a variable inside `x % n` only if its definition is a remainder (the
unsigned variables of C), not a polynomial over atoms: `zz == 2 * count(...)` does not reduce `zz % 2`
(examples/dafny/teq/counters_phase_mod.dfy, if `current_trace_step_or_keep` replaces the forward lemma). (b) `t div k`
and `t mod k` are unrelated atoms of the simplex: `SIZE % 2 == 0`, `SIZE / 2 == i`, `2 * i < SIZE` is not refuted
(array-tiling/tcpy).

**Change.** (a) In `Simplify.remainders`, also variables whose definition in the context is a polynomial, excluding
definitions that mention the variable (as now). Done in the restricted form: only definitions that are constant modulo
`n`, since a general substitution may cycle (`x == y + 2`, `y == x - 2`: `x % 2` becomes `y % 2` and back);
counters_phase_mod.dfy and mono-crafted_12 are proved with the rule, pr2 and mbpr2 stay open. (b) When an atom `t div k` or `t mod k` with a literal `k != 0` enters
the arithmetic, its definition is assumed once: `t == k * (t div k) + t mod k`, `0 <= t mod k < |k|`. Done (0.52.15) in
`Linear.add`, replacing the separate bounds of quotients and remainders; it proves tcpy and diff-2-n-u.

**Database.** `current_trace_step_or_keep` in aggregation.dfy (the value `x + a * count(true, bs)`, a rewrite rule)
replaces the forward lemma `current_trace_step_or_keep_mod` of counters.dfy, whose trigger is a raw trace pattern
(done, Oct 27); no forward lemmas for division.

**Tests.** counters_phase_mod.dfy, mono-crafted_12 (7 s with the rewrite rule instead of 41 s), array-tiling/tcpy;
pr2, mbpr2 need the parity of successors in addition (`(i + 1) % 2` against `i % 2`), left open.

## 5. Higher-order values at arithmetic arguments (diagnosis open)

**Gap.** With the index in normal form (`-k + m + -1`), the pattern `a[-k + m + -1 := F(-k + m + -1)][k := F(k)]`
does not match the copy from both ends, while `a[-k + m + -1 := b[-k + m + -1]]` does; the database has one lemma per
kind of source (`select_current_trace_copy_both_ends(_list)`). Patterns are in normal form by the database, not by
reading. Candidates: the instance of the argument after substituting `m` is compared literally in
`Rewrite.abstraction` and is not in normal form (the summands are ordered by their atoms), or the value is matched
before the index binds `m`. Ruled out with step 2 on `acopy[SIZE-i-1] = 2 * a[SIZE-i-1]; acopy[i] = 2 * a[i]`: the
pattern is flat as the goals are, and no argument with unbound variables is reported, so `m` is bound in time. Left:
the conditions of `Rewrite.abstraction` (`replaced.forall(...)`, the check against `avoid`), the next place for a
debug line; until then the two lemmas stay.

## Database work (no change of the engine)

- Done (Oct 27): the four forward lemmas whose triggers are any read and whose other variables are bound by
  conditions alone (search.dfy: `earlier_agree_prefix`, `earlier_not_occurs_prefix`, `earlier_above_iterations`,
  `select_not_occurs_selects`) are rules on the comparisons of the reads (`earlier_eq_prefix`,
  `earlier_eq_not_occurs_prefix`, `earlier_above_iterations`, `select_eq_not_occurs_selects`), as
  `invs_select_store_ne` for the sentinel, and the fold `agree_prefix` is the equation of prefixes
  (`invs_agree_prefix`). With `current_trace_step_or_keep` and on 0.52.13, the VerifierCloud (Ryzen, 120 s) gains 5
  tasks of Arrays and 5 of Loops and loses none. Caveats: the binding of `n` takes the first matching fact; a rule is
  stated in the orientation of the atom as the goals contain it (`j < earlier(j, ts)`, not `earlier(j, ts) <= j`),
  since negations are not normalized into the other comparison everywhere; `earlier_eq_not_occurs_prefix` needs
  `n <= length xs` (Lean, lean/premises.txt), which the loop provides.
- The comments of the review of Oct 26: usage annotations out of date (`current_maxs_earlier`, `current_mins_earlier`
  unused since the prefix variants; `count_consts`, `count_true_eq`, `counts`, `invs_not_or` no longer used by the
  tasks named), module headers.

## Not done, and why

- **Instantiating iteration constraints at reads** (an `invs` fact at the positions read in the goal): quantifier
  instantiation by the engine, which the design avoids; an iteration constraint is never a side condition, since
  deciding it builds the contexts of the `invs` facts, whose reads would match again (doc/teq.md), and instances
  simplified at every firing cost as the forward lemmas showed. Rules on the atoms instead (above).
- **Terms with binders compared modulo bound names in the classes**: too complicated (re-keying binder nodes on every
  merge); the workaround of `compacts` and `filters_*` (the count as a variable of the conditions) stays.
- **Sums in patterns** (the empty sum, several summands, literal coefficients): `Rewrite.matchesSummands` matches the
  fixed summands first and restricts the variables on purpose (no empty sum outside of sums, negated variables only
  negative summands, higher-order summands as a fallback), each against a loop such as `x + 1` matching `1` with
  `x = 0`; the lemmas that work around it (`maps_counter_scale`, `select_current_trace_prefix_sums_add`,
  `select_current_trace_ahead_down`, `mul_lt_cancel`) are cheap and stay.
- **Forward lemmas for division and parity** (`div_mod`, `mod2_succ`): triggers at every division, presumably the cause
  of 10 timeouts of Loops with the fallback; step 4 instead.

## Order

1, 2 done (0.52.9), 3 failed and reverted (0.52.10), 4 done (0.52.15), the database work done (Oct 27); open: 3b
(the prototype and its measurement; nr2-nr5 wait for it), 5 once diagnosed.
