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

## 3. Variables kept instead of literals (done, 0.52.9; measured in the cloud)

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

## 4. Remainders and division

**Gaps.** (a) `Simplify.remainders` substitutes a variable inside `x % n` only if its definition is a remainder (the
unsigned variables of C), not a polynomial over atoms: `zz == 2 * count(...)` does not reduce `zz % 2`
(examples/dafny/teq/counters_phase_mod.dfy, if `current_trace_step_or_keep` replaces the forward lemma). (b) `t div k`
and `t mod k` are unrelated atoms of the simplex: `SIZE % 2 == 0`, `SIZE / 2 == i`, `2 * i < SIZE` is not refuted
(array-tiling/tcpy).

**Change.** (a) In `Simplify.remainders`, also variables whose definition in the context is a polynomial, excluding
definitions that mention the variable (as now). (b) When an atom `t div k` or `t mod k` with a literal `k != 0` enters
the arithmetic, its definition is assumed once: `t == k * (t div k) + t mod k`, `0 <= t mod k < |k|`.

**Database.** `current_trace_step_or_keep` in aggregation.dfy (the value `x + a * count(true, bs)`, a rewrite rule)
replaces the forward lemma `current_trace_step_or_keep_mod` of counters.dfy, whose trigger is a raw trace pattern;
no forward lemmas for division.

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

- The four forward lemmas whose triggers are any read and whose other variables are bound by conditions alone
  (search.dfy: `earlier_agree_prefix`, `earlier_not_occurs_prefix`, `earlier_above_iterations`,
  `select_not_occurs_selects`) become rules on the atoms that the goals contain, as `invs_select_store_ne` for the
  sentinel. Tried for `agree_prefix`: the fold replaced by the equation of prefixes (`invs_agree_prefix`) and a rule
  on the comparison of the reads (`earlier_eq_prefix`, `n` bound from the facts) prove standard_compare_ground,
  standard_copy1_ground-1 and standard_two_index_01 (local, Oct 26); the binding of `n` takes the first matching fact.
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

1, 2, 3 done (0.52.9); next: the cloud result of 3 (then `stores_cases_point` out), 4, the database work, 5 once
diagnosed.
