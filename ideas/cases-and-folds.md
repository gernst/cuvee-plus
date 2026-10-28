# Cases instead of conditionals, and named folds

**Status.** Sections 1-3 are implemented (Oct 28, documented in doc/prove.md), `stores_index_cases` removed (section
8); sections 4-6 are settled from the `:used` lists of the cloud run of 0.53.10 (Oct 28, below), open are only the
engine gaps mbpr4 and nr2-nr5, which need Scala. Decided and done (Oct 28): the right-hand sides of the lemmas are
choices (section 2, "Open"; 34 lemmas of teq.dfy and the modules, with the term syntax `if { case ... }` in the Dafny
parser, not yet in Boogie); the scalar version of the reset and accumulation, and `sum_above`, `sum_below` instead of
the shape lemmas of sums (section 7). The patterns that match nearly any trace (section 5) are left as they are.

A plan (Oct 28, 2026) that follows 0.53.1, which made the strided stores folds (`strides₂` to `strides₅`) whose values
the matcher synthesizes per case (doc/prove.md, "Rewriting"; [conditional-stores.md](conditional-stores.md)). That
change left two forms of the same thing: values per case as `maps` with cases, and the right-hand sides of the
database written with if-then-else. The plan settles on cases, and lists the further raw traces of the database
that could become named folds. Measured on the cloud only (Arrays and Loops against 0.53.0, by the user).

## 1. Cases instead of if-then-else in `maps`

**Now.** Conditionals in the results of a trace are lifted into cases (`Simplify.choices`), those in the update of a
`maps` are not (`Simplify.maps`). A fold with values per case gives `maps(... :: case P(k) => c case !P(k) => d)`, the
lemma `stores_index_cases` (arrays.dfy) gives `maps(... :: if P(k) then c else d)`: the same values in two forms, and
the fold `stores` (teq.dfy, before all modules) now subsumes the lemma while it is tried first, against the rule of
doc/teq.md that a rule whose pattern subsumes another comes after it.

**Change.** `Simplify.maps` lifts the conditionals of its update into cases with the same `choices` as traces. Both
forms are then one term, so `stores_index_cases` is redundant and goes, after `scripts/missing.py` on the cloud logs
shows that brs2-brs5 apply the fold instead. Lemmas whose right-hand sides have conditionals inside a `maps` but whose
left-hand sides catch shapes the fold does not (a value or guard that reads the array, a case that keeps the array)
stay, with their right-hand sides in cases: `stores_cases`, `select_current_trace_reset_add`,
`select_current_trace_reset_add_keep`.

**Not needed.** Trying all rules exactly first and per case only afterwards: with one form, the fold and the specific
lemma agree, and the specific shapes that remain are not subsumed by a fold.

## 2. Reading a map with cases: cases, not if-then-else

**Now (0.53.1, provisional).** `earlier(j, maps(...))` of an update with cases is turned into conditionals that end
in `unspecified` (`Simplify.earlier`), and conditionals are lifted over equations (`Simplify.eq_`), which decides
e.g. `(if x != c then x else d) != c` for `c != d` (examples/dafny/teq/strides.dfy, `defaults`).

**Change.** Revert the conditionals at `earlier`: the choice stays, and is lifted out of its atom into cases,
`A[eps(cᵢ => vᵢ)]` as the conjunction of `cᵢ ==> A[vᵢ]`, which is `Normalize.choices`, so far used for side conditions
only (`Rewrite.holds`); now also for the atoms of goals and facts. The goal of `defaults` then reads
`(e != c ==> e != c) && (e == c ==> d != c)`. Cost to watch: every atom with a choice is split.

**Open.** The lifting of if-then-else over equations stays useful as long as the right-hand sides of read lemmas are
conditionals (`if 0 <= j < n then ... else a0[j]`); whether those are written as cases too is a separate decision,
since it touches many lemmas. Whether conditionals and cases should leave comparisons and products (motivex) as well
is open too.

**Regression (0.53.6, cloud).** mbpr4, SV-LIB bhmr2007, loopv1 and loopv3 end in unknown: a definition whose value
contains a choice, e.g. `a == x0 + n * eps(c => 1, !c => 2)` from `maps_const` and `sums_consts`, is lifted into the
conjunction `(c ==> a == ...) && (!c ==> a == ...)`, which the case split of `-prove` does not take apart, where the
conditional of 0.53.5 was split (also with a further `-split -prove`). The proposed fix lifts a choice out of an atom
into the nested conditional `ite(c₁, A[v₁], ite(c₂, A[v₂], ... A[unspecified]))`, the form the rest of `-prove`
handles, while the cases stay cases in updates, maps and the right-hand sides of lemmas (TODO.md).

## 3. Keys stay keys

A bound variable of a synthesized dependency that is the index of a store takes no values per case
(`Rewrite.update`): otherwise `case k != c => a[k := F(k)] case k == c => a[c := F(c)]` (copysome2-1,
`stores_cases_point`) folds into `stores` with keys `maps(... :: case k != c => k case k == c => c)`, a map that no
simplification merges back into the counter, so the read lemmas over counters no longer apply. Only stored values and
guards take cases.

## 4, 5. Overlaps among the lemmas, raw traces without a fold

Moved to [database.md](database.md) (Oct 28).

## 6. Other open points of the strided stores

- The Lean proofs of `select_current_strides₂` to `₅`: done (Oct 28).
- The stores ahead as `strides₂` at stride 1 with a read lemma for overlapping windows (the last writer wins); the
  last iteration of rewnif stores one cell only, which a fold of two cells does not cover.
- nr2-nr5: the iteration variable written as the literal it equals in each case ([engine-gaps.md](engine-gaps.md),
  gap 3).
- The cancellation of constant offsets in sums (0.53.1) applies to all rules; the tasks whose rules match differently
  since are found by `scripts/missing.py` on the cloud logs.

## 7. Found while implementing 1-3

- Patterns with a fixed number of cases break where the simplifier merges cases of equal values (80430b9b): brs2-brs5
  have the values `case 0 < k && k % 2 == 0 => 2 case 0 < k % 2 || k == 0 => 0`, the three cases of
  `sum_cases_below` merged into two. Replaced (Oct 28) by `sum_above` and `sum_below` (aggregation.dfy): a sum over a
  counter of `n` iterations is at least or at most `e` if each value times `n` is, whatever the number of cases, which
  binds no bound of the values; brs2-brs5, ms2-ms5 and loop-invgen/large_const (lost with the cases in `maps`, a lower
  bound was missing) proved locally. `sum_mod_below` stays, since `n * (k % m)` is not linear.
- A choice nested in a term of a trace's update is lifted into cases like a conditional (`Simplify.choices`, done):
  the sum of brs2 in a scalar instead of the cell `sum[0]` had `if { case k % 2 == 0 => 2 case 0 < k % 2 => 0 } + S`
  in its update; with `current_trace_reset_add_keep` (aggregation.dfy), the scalar version of
  `select_current_trace_reset_add_keep`, it is proved (examples/dafny/teq/sum_cases.dfy).

## 9. Choices in terms: lifting by polarity (implemented Oct 28, doc/prove.md)

**Status.** Implemented (0.53.9): bhmr2007, loopv1, loopv3 recovered on the cloud. The case where no guard holds,
proposed below for guards that are not exhaustive, lost large_const in 0.53.9 (the side condition of `sum_above` lacks
the iteration constraint that makes its guards complete) and was removed by decision: the guards are complete in
context. mbpr4 open (below).

A choice `eps(cᵢ => vᵢ)` in a term is reasoned about only by a case analysis on its guards. Since 0.53.6 that analysis
happens in the wrong form at some places and not at all at others:
- facts: `Simplify.atom` turns a definition with a choice into the conjunction `(c ==> a == ...) && (!c ==> a == ...)`,
  which neither the case split of `-prove` nor `-split` takes apart (the losses of 0.53.6: mbpr4, SV-LIB bhmr2007,
  loopv1, loopv3; TODO.md);
- side conditions: the bodies of `invs` need the lifting case by case, `sum_above` and `sum_below` depend on it
  (removing `Simplify.atom` lost brs2-brs5, large_const, sum_cases, sum_above; tried and reverted);
- `-split` does not lift choices (lifting them in `Normalize.lift` and splitting a choice of formulas per case in
  `Split` recovered bhmr2007, loopv1, loopv3 with `-split` alone; tried and reverted with the rest).

**Principle.** A choice in an atom is lifted to the level of formulas in the form that fits the position of the atom;
for exhaustive and disjoint guards the forms are equivalent, they differ in which part of the engine takes them apart:

| Position of the atom | Form | Taken apart by |
|---|---|---|
| goal (positive) | `⋀ᵢ (cᵢ ==> A[vᵢ])` | the simplifier, conjunct by conjunct; `-split` per conjunct |
| fact (negative) | `⋁ᵢ (cᵢ && A[vᵢ])`, the DNF | the case split of `-prove` on disjunctive facts (up to three disjuncts); `-split` among the antecedents |
| in a combinator or a side condition (neutral) | `⋀ᵢ (cᵢ ==> A[vᵢ])`, pointwise | the simplifier, as before |

- A choice that is the value of all elements of a list or a trace stays, e.g. `consts(n, eps(...))`, read element by
  element by the read lemmas (the existing exception of `Simplify.atom`).
- Not taken (0.53.9, removed): the case where no guard holds, `A[unspecified]`; the guards are complete in context.
- Places: `Simplify.atom` with the polarity of the context (`ctx.polarity`); `Normalize.lift` lifts conditionals and
  choices alike for `Split`, which splits a choice of formulas per case in conclusions and antecedents; no special case
  in `Prove.alternatives` (by decision); implications among the antecedents stay implications (by decision).

**Expected.** bhmr2007, loopv1, loopv3: the definition `a == ... eps(nondet != 0 => ...)` becomes the fact
`(c && a == n) || (!c && a == 2 * n)`, which both `-prove` and `-split` split; sum_above, sum_below: the side
conditions are neutral, as before 0.53.6. mbpr4 is a goal position as in 0.53.6 and needs more: its residual goal
`i == 1 || (i + 2) % 4 == 0 || ... || 3 <= i` needs the case split on the two values of `i`, whose bound `i < 3` is a
negated disjunct of the conclusion, not a premise, which the split on two-valued variables does not see.

**Cost.** A fact in DNF is no equation of the classes until it is split, so a definition reaches the matcher only in
the cases; several choices multiply the cases, bounded by the depth of the split (4) and by `-split`.

## 8. A review of the database

Moved to [database.md](database.md) (Oct 28).

## Steps

1. Sections 1-3 in one change (Simplify, Rewrite), the examples regenerated, the jar for a cloud run of Arrays and
   Loops against 0.53.0.
2. `stores_index_cases` dropped once `scripts/missing.py` shows the fold in its place; the order of the reset lemmas
   (section 4) after checking with `-debug match`.
3. Section 5 group by group, on request.
