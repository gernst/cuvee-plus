# Cases instead of conditionals, and named folds

**Status.** Sections 1-3 are implemented (Oct 28, documented in doc/prove.md), except that `stores_index_cases` is
kept until the cloud run; sections 4-6 are open. Decided and done (Oct 28): the right-hand sides of the lemmas are
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

## 4. Overlaps among the lemmas (as of 0.53.1)

From the patterns, not measured:
- `select_current_trace_reset_add_keep` (aggregation.dfy) may cover `reset_add` and `reset_keep` (arrays.dfy) with
  the guard variable `P` true or false, depending on how `Rewrite.guard` treats `!P(k)`; aggregation comes before
  arrays, so the subsuming lemma is tried first. To check with `-debug match`; then the specific lemmas first.
- `select_current_trace_conditional_store_deps` covers `conditional_store` (the dependencies share the counter's
  bound variable); the specific one comes first already.
- `counts_true` covers `current_trace_step_or_keep` with `a = 1`, before it; the values agree.
- `recurrence` and `prefix_sums` are the same recurrence `b[i] = b[i - 1] + G` over one counter or two;
  `prefix_sums_add` exists since a higher-order summand takes one summand only.
- `copy_both_ends` and `copy_both_ends_list` are one shape with the source an array or a list.
- `current_trace_increasing` and `current_trace_bounded` match any trace of up to four cases of their result forms;
  they state facts and do not preempt.

## 5. Raw traces without a fold

Lemmas that read a value off a raw `trace(...)`, grouped by the shape they share; a named trace function per shape,
with one read lemma, as for `strides₂`, would replace the group. Each group is measured before its shape lemmas go,
since a direct read lemma costs one rewrite step and a fold two or more.

| Shape | Lemmas |
|---|---|
| shift `x[k := x[k + 1]]` over `counter(i, 1, n)` | done (Oct 28): the fold `shifts(a, keys)` of teq.dfy with its accessors, and `select_current_shifts`, `elems_selects_shift`, `elems_selects_rotate` over it; the fold fires on bAnd1, the users take about 30 s, to be confirmed on the cloud |
| reset and accumulate at one cell, `case k == 0 => a[j := c] case 0 < k => ...` | `select_current_trace_reset_keep`, `_reset_add`, `_reset_add_keep` |
| recurrence `b[i := b[i - 1] + G]` | done in part (Oct 28): the fold `scans(a, keys, values)` (aggregation.dfy) with `select_current_scans` replaces `_prefix_sums` and `_prefix_sums_add`, also for the form over two counters, whose store index `i` the pattern `p + 1` reaches through `i == k + 1` (eqn1, eqn2, nsqm, sqm, standard_seq_init_ground correct; with `prefix_consts` of teq.dfy); `select_current_trace_recurrence` (a reset at 0, the read `a[i - 1]`) stays until `phases` splits off the first iteration |
| two phases `x + 1` up to `b`, then `x + c` | done (Oct 28): `phases(x0, m, n, F, G)` (counters.dfy), the first `m` iterations by `F`, the others by `G`, introduced by `trace_threshold` and read by `current_phases` (the two phases composed over counters from 0) and `invs_phases_upper` (increasing steps); declared without a body, since as a fold it took switches at an iteration from `current_trace_step_or_keep` (counters_phase_mod); `current_trace_two_phases`, `invs_two_phases`, and `current_trace_increasing` (preempted by the fold `sums`) removed; Mono1_1, mono-crafted_6, _11, phases_1 unchanged |
| copy from both ends `a[m - k - 1 := ...][k := ...]` | done (Oct 28): the fold `copies(a, ks, ls, S)` with `select_current_copies` (arrays.dfy), the source `S` an array or a list, with `occurs_counter_down` and `maps_counter_neg` of teq.dfy; tcpy, array_tiling_tcpy correct, faster |
| conditional store keeping the array otherwise | done (Oct 28): the fold `stores_where(a, keys, guards, values)`, `case g => b[k := v] case !g => b`, with the guards and values synthesized over any dependencies, replaces `_conditional_store` and `_deps` (a synthetic example with a choice as the guard proved, which `_deps` did not); `select_current_stores_where_first` replaces `select_current_trace_reset_keep`, which the fold takes first (ms1, ms1f); the matcher bug it exposed (a shared front of another type, bugs.md) is fixed; `select_current_trace_cap` stays, its guard reads the array; copysome*, array_mul_init, condn take 25-50 s, to be confirmed on the cloud |
| accumulation at a key, histogram | `current_trace_add_at`, `current_trace_histogram` |
| conditional step, geometric product, counters | `current_trace_step_or_keep`, `current_trace_geometric`, `current_trace_catch_up`, `current_trace_flag` |
| stores ahead (windows of width 2 at stride 1, the last iteration shorter) | `select_current_trace_ahead`, `_ahead_down` |

Patterns that match nearly any trace (a variable for the whole update): `perm_swaps`,
`perm_steps_three`, `sorted_prefix_steps`, `sorted_prefix_steps_two`; they apply only at the atoms `perm(...)` and
`sorted(...)`, but they are the kind of lemma that should not match an arbitrary update.

## 6. Other open points of the strided stores

- The Lean proofs of `select_current_strides₂` to `₅` (lean/open.txt still lists the removed defaults).
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

## 8. A review of the database (Oct 28)

- Removed: `stores_index_cases` (the fold `stores` with values per case gives the same term, brs2-brs5 apply it),
  `select_store_other` (decided by `Simplify.select` with the facts; its tasks do not parse, bugs.md),
  `perm_swaps_one`, `perm_steps`, `perm_steps_two` (covered by `perm_swaps` and `perm_steps_three`, whose further
  dependencies share the bound variable of the first; the answers of the sorting examples unchanged).
- Kept: `store_select_other` (the equation of two arrays is not decided without it), `invs_not_or` (a negated
  disjunction is not pushed into `invs`), `occurs_counter_up` and `indexof_counter_up` (`(j - i) % 1` simplifies now,
  but the step versions need `0 <= n` and are in counters.dfy, not in the core; to measure), `sum_indicator_true` and
  `_false` (a general `sum_cases_two` rewrites the sum before `sum_below` sees its comparison, brs2-brs5 lost).
- Deferred: the bounds by `max` and `min` through membership, one parity fact for the triangles.
- Added: the accessors of the folds of aggregation, `earlier` and `prefix` of `maxs`, `mins`, `parities`, `prefix` of
  `counts`, as those of `sums` (uniform, they cost nothing where they do not match).
- Not taken: `perm` and the equality of multisets are not unified, since `perm` relates whole arrays by a bijection of all indices, while a multiset needs a finite list of
  keys.

## Steps

1. Sections 1-3 in one change (Simplify, Rewrite), the examples regenerated, the jar for a cloud run of Arrays and
   Loops against 0.53.0.
2. `stores_index_cases` dropped once `scripts/missing.py` shows the fold in its place; the order of the reset lemmas
   (section 4) after checking with `-debug match`.
3. Section 5 group by group, on request.
