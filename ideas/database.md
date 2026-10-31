# The lemma database: open points, workarounds, decisions

One place for the ideas about the lemma database of `-teq` (teq.dfy and the modules of
[resources/cuvee/teq](../resources/cuvee/teq)), merged on Oct 28, 2026 from database-review.md, array-lemmas.md and
the sections on the database of engine-gaps.md, on Oct 31 also from cases-and-folds.md and conditional-stores.md; the
engine's side and nla-digbench are [engine.md](engine.md). The
open tasks by family, with the concept each needs, are in [open-tasks.md](open-tasks.md); the work queue is in
TODO.md. Usage is counted by `-rules` over the results of Cuvée ([scripts/rules.py](../scripts/rules.py)); a lemma that
at most three proved tasks use names them on its `(from ...)` line (doc/teq.md).

## Raw traces and named folds

Lemmas that read a value off a raw `trace(...)` are grouped by the shape they share; a named trace function per shape
with one read lemma, as for `strides₂`, replaces the group. A group is measured before its shape lemmas go, since a
direct read lemma costs one rewrite step and a fold two or more.

| Shape | State |
|---|---|
| adjacent stores per iteration | the folds `strides₂` to `strides₅` (strides.dfy), values per cell synthesized per case by the matcher; one fold per number of cells, the number of cases is free |
| shift `x[k := x[k + 1]]` | the fold `shifts(a, keys)` (teq.dfy) with `select_current_shifts`, `elems_selects_shift`, `elems_selects_rotate` |
| recurrence `b[i := b[i - 1] + G]` | the fold `scans(a, keys, values)` (aggregation.dfy) with `select_current_scans`, also over two counters; `select_current_trace_recurrence` (a reset at 0, the read `a[i - 1]`) stays until `phases` splits off the first iteration |
| two phases, `F` for the first `m` iterations, `G` after | `phases(x0, m, n, F, G)` (counters.dfy), introduced by `trace_threshold`, read by `current_phases` and `invs_phases_upper`; without a body, since as a fold it took switches at an iteration from `current_trace_step_or_keep` |
| copy from both ends | the fold `copies(a, ks, ls, S)` with `select_current_copies` (arrays.dfy), the source an array or a list |
| conditional store keeping the array otherwise | the fold `stores_where(a, n, guards, values)` over the counter (arrays.dfy); with the keys as a list (0.53.7) it took the compactions from `filters_above` and lost standard_partition_ground-2, so the keys are the counter; `select_current_trace_reset_keep` (a reset at one position) and `select_current_trace_cap` (its guard reads the array) stay |
| reset and accumulate at one cell | kept as three shape lemmas (`_reset_add`, `_reset_add_keep`, `_reset_keep`): they differ in their number of cases, so a fold would need an introduction per form; each has its tasks |
| accumulation at a key, histogram | kept: `current_trace_add_at`, `current_trace_histogram` |
| conditional step, geometric product, counters | kept: `current_trace_step_or_keep`, `current_trace_geometric`, `current_trace_catch_up`, `current_trace_flag` |
| stores ahead (windows of width 2 at stride 1, the last iteration shorter) | `select_current_trace_ahead` (rew, rewnif), `_ahead_down` restated over the first counter (rewnifrev, Oct 28); the windows as an overlapping `strides₂` not taken, the read of a cell that two iterations write is the shape itself |

Patterns that match nearly any trace (a variable for the whole update): `perm_swaps`, `perm_steps_three`,
`sorted_prefix_steps`, `sorted_prefix_steps_two`. They apply only at the atoms `perm(...)` and `sorted(...)`, but
they are the kind of lemma that should not match an arbitrary update; left as they are.

## Overlaps among the lemmas

From the `:used` lists of the cloud run of 0.53.10: the specific lemmas fire where they apply, the general ones do not
preempt them (`_reset_add` on brs1, ms2, ms3; `_reset_add_keep` on brs2-brs5; `_reset_keep` on ms1;
`current_trace_step_or_keep` on 8 tasks, `counts_true` on 17 others; `select_current_trace_recurrence` and
`select_current_scans` on disjoint tasks). From the patterns:
- `select_current_trace_reset_add_keep` (aggregation.dfy) may cover `_reset_add` and `_reset_keep` (arrays.dfy) with
  the guard variable true or false, depending on how `Rewrite.guard` treats `!P(k)`; aggregation comes first.
- `counts_true` covers `current_trace_step_or_keep` with `a = 1`, before it; the values agree.
- `current_trace_bounded` matches any trace of up to four cases of its result forms; it states facts and does not
  preempt.

## What could be unified

- **Membership in a counter.** `occurs_counter_up` and `indexof_counter_up` (teq.dfy) are the step versions at step 1
  (`occurs_counter_step`, counters.dfy); `(j - i) % 1` simplifies now, but the step versions need `0 <= n` and are not
  in the core; to measure.
- **Disjunction-free variants** (`invs_counter_upper_nonnegative` beside `invs_counter_upper`, `invs_mods_upper` and
  `invs_mods_down` beside their `_cases`, `invs_counter_mod_upper_zero` beside `_cases`): each removes the
  disjunction `n <= 0 || ...` by a side condition, since a disjunction is not split in the context of a combinator.
- **Folds that are not possible.** `counter_def` (the counter is the dependency of its own trace) and `consts_def`
  (over a counter of any start and step, while a fold abstracts its formals only).
- **`perm` and the equality of multisets** are not unified: `perm` relates whole arrays by a bijection of all indices,
  a multiset needs a finite list of keys.

## Workarounds for gaps of the engine

Lemmas or shapes of lemmas that exist because the matcher or the engine lacks something; each could go once its gap
is closed (the gaps of the engine: [engine.md](engine.md)). Tests of the workarounds: examples/c/teq
(compacts.c, max_seeded.c, copy_both_ends.c).

| Gap | Lemmas |
|---|---|
| a higher-order instance must contain the term it abstracts: no constant functions | `stores_cases` (its first case stores a constant) |
| terms with binders compared literally by the arithmetic, not modulo bound names; `⌊K⌋` and `⌊counter(0, 1, n)⌋` not identified below a binder | the folds `compacts`, `filters_above`, `filters_below` with the count as a variable of the conditions and the keys a list |
| a sum pattern `a + b * v` gives no variable the empty sum 0 | `maps_counter_scale` beside `maps_counter_affine` |
| literals in patterns: a coefficient is not matched by a variable | `mul_lt_cancel`, reverse.dfy (the step as a variable) |
| guards on booleans are not identified with `b == true` | `counts_false`, `counts_true` (false first) |
| the disjunction `n <= 0 \|\| ...` is not split in the context of a combinator | the disjunction-free variants above |
| an iteration constraint as a side condition recurs through its own fact | atoms for constraints: `invs_agree_prefix` (the equation of prefixes), `above_iterations`, `!occurs(e, prefix(...))`; the facts at the reads as rules on the comparisons of the reads (`earlier_eq_prefix`, `earlier_eq_not_occurs_prefix`, `select_eq_not_occurs_selects`) instead of forward lemmas triggered at every read |
| a rule variable must not capture a bound variable of the expression | the dependency `hs` of lemmas whose body reads it through a higher-order variable `D(k, h)` (`current_trace_flag`, `count_false_true`, `count_true_eq`, `stores_read_unmodified`) |
| an equation of integers as a lemma rewrites its left-hand side as a term | `double_eq_half` (an equivalence of atoms) |
| complete guards are an obligation of the proofs | the complementary last case of `current_trace_bounded`, `bisection` |
| the engine does not check reads within the loop or lengths | the premises of [lean/premises.txt](../lean/premises.txt) |
| a pattern of nested stores has a fixed number of stores | the folds `strides₂` to `strides₅`, one per number of adjacent cells |
| a pattern has a fixed number of dependencies, and a polymorphic higher-order side condition is not matched | `perm_steps_three`, `perm_swaps` (further dependencies share the bound variable of the first); Lean proves them from one lemma over any list of dependencies (`perm_steps_general`) |
| a pattern with a fixed number of cases breaks where the simplifier merges cases of equal values | `sum_above`, `sum_below` (any number of cases, binding no bound of the values) instead of `sum_cases_below`; `sum_mod_below` stays, `n * (k % m)` is not linear |

The engine gaps behind these, as suggestions (from the review of Arrays, Oct 26): compare terms with binders modulo
their bound names in the arithmetic and the classes (also sumt2); congruence through binders, `map(k in ⌊K⌋ ...)` and
`map(k in ⌊counter(0, 1, n)⌋ ...)` for `K == counter(0, 1, n)`; higher-order variables applied to terms that are not
bound variables, once another case or store binds them; `ite(c, 1, 0) != 0` of `assume_abort_if_not` simplified to
`c` inside `invs` (array_init_nondet_vars, pair_symmetr2); reading an iteration constraint at a witness `0 <= x < n`
(standard_vararg, array_init_nondet_vars, standard_sentinel-2).

## Cases and choices

Settled on Oct 28 (0.53.1 to 0.53.10, documented in doc/prove.md): one form for values per case.
- `Simplify.maps` lifts the conditionals of its update into cases, as traces do, so a fold with values per case and a
  lemma with conditionals give one term; `stores_index_cases` went.
- The right-hand sides of the lemmas are choices (`if { case ... }`, parsed by Dafny, not yet by Boogie); a choice in
  an atom is lifted to the level of formulas by the polarity of the atom (0.53.9: in goals and neutral positions the
  conjunction of `cᵢ ==> A[vᵢ]`, among the facts the disjunction of `cᵢ && A[vᵢ]`); the guards are complete in
  context, a case for no guard lost large_const and was removed.
- Keys stay keys: a bound variable of a synthesized dependency that is the index of a store takes no values per case
  (`Rewrite.update`); otherwise `case k != c => a[k := F(k)] case k == c => a[c := F(c)]` folds into `stores` with
  keys `maps(... :: case k != c => k case k == c => c)`, which no read lemma over counters matches. Only stored values
  and guards take cases.
- A choice nested in a term of an update is lifted like a conditional; the scalar version of the reset and
  accumulation, `current_trace_reset_add_keep`, proves the sum of brs2 in a scalar (examples/dafny/teq/sum_cases.dfy).

Open: mbpr4 (engine.md, 5.3) and nr2 (engine.md, 4.2).

## Conditional stores (history)

A loop body with `s` conditional stores, each choosing a value by a guard that does not depend on the iteration,
becomes an update with `2^s` cases, one per path of `-teq` (pr3-pr5, see
[benchmarks/monocera/summary.md](../benchmarks/monocera/summary.md)):

```
trace(a0, for ⌊counter(0, 1, n)⌋ do a, k ::
  case 7 >= m && 3 >= m => a[2 * k := 7][2 * k + 1 := 3]
  case 7 >= m && !(3 >= m) => a[2 * k := 7][2 * k + 1 := 0]
  case !(7 >= m) && 3 >= m => a[2 * k := 0][2 * k + 1 := 3]
  case !(7 >= m) && !(3 >= m) => a[2 * k := 0][2 * k + 1 := 0])
```

**Taken (0.53.1, Oct 28).** The folds `strides₂` to `strides₅` with one list of values per cell; the matcher matches
a pattern without cases against the cases of an update one by one, the bound variables of the synthesized dependencies
take a value per case, and the map gets the cases of the update (`Rewrite.update`). pr3-pr5, pnr2, pnr3 proved by
0.53.10. The conditional stores that keep the array otherwise are the fold `stores_where` over the counter.

**Rejected or not adopted:**
- Merging the cases into stores of conditional values in the simplifier (`Simplify.eps`), by decision (Oct 27): the
  case distinction of an update is what the lemmas match. Measured before: pr3 proved, rew and ms2 lost (a store of a
  choice of arrays; a reset and an accumulation at one cell merged into one value). The variant as a local step on
  `Eps` is engine.md, 5.2.
- The merge as a rewrite rule (`trace_merge_store`, Oct 11): it applies to one conditional cell, but a pattern with two
  cases cannot cover four cases pairwise, so a rule per number of cells and order of guards would be needed.
- The merge in `-teq` (a conditional whose branches store at the same index kept as a store of a conditional value):
  avoids the `2^s` paths and the overflow at ten conditionals, but only for that shape; not implemented.
- Shape lemmas per number of cases (`select_current_trace_stride3_cases4` to `stride5_cases6`): removed in 0.53.1.
- A generic lemma over the window of an iteration (measured Oct 28, not adopted): a loop whose iteration `k` changes
  only the cells of its window, by any number of cases, leaves at `j` what iteration `j / s` stores there.

  ```
  lemma {:rw} {:teq} select_current_trace_window2(a0: array<int, int>, n: int, j: int, U: (array<int, int>, int) -> array<int, int>)
    requires forall b: array<int, int>, k: int, i: int :: i != 2 * k && i != 2 * k + 1 ==> U(b, k)[i] == b[i]
    requires forall b: array<int, int>, c: array<int, int>, k: int :: U(b, k)[2 * k] == U(c, k)[2 * k] && U(b, k)[2 * k + 1] == U(c, k)[2 * k + 1]
    ensures current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: U(a, k)))[j]
      == if 0 <= j < 2 * n then U(a0, j / 2)[j] else a0[j]
  ```

  pr2 in 46 s (10 s with the shape lemma), but its pattern matches every trace of an array over a counter, whose
  quantified conditions are evaluated at every read: pr3 and nr2 do not finish in 90 s. A cheap first condition that
  recognizes an update writing only its window from its shape would make it the principled form.

Left of the kind: `stores_cases` (its first case stores a constant, since a higher-order instance must contain the
term it abstracts), `select_current_trace_cap` (its guard reads the array), `select_current_trace_reset_keep`; mods
and modsf (strided, no fixed number of cases). A sum with a conditional increment (`case C => x + f(k) case !C => x`)
is the same merge for `sums` ([iterator-profiles.md](iterator-profiles.md)).

## The lemmas of examples/dafny/algorithms

- **Candidates, not moved**: the bounds of `maxs` over `selects` (`select_le_maxs`, `occurs_maxs` of max_element); the
  fold `argmaxs` with its bounds (argmax.dfy); `invs_pairs` of reverse.dfy as an affine bound of a counter;
  `sum_selects_zero` (prefix_sums.dfy). None occurs in SV-COMP.
- **Copies left**: cocktail_sort, three_way_partition, merge, counting_sort copy predicates of `teq:sorted`; they time
  out with and without the copies.
- **Specific to their programs**, staying local: the folds and inductions of the sorting algorithms (`bubble_pass`,
  `insert_pass`, `shake`, `lomuto`, `threeway`, `bubbled`, ...), merge (`merged`), counting_sort (`rank_table`),
  distinct and first_duplicate (`nodup`, `scan`), transpose, reverse (`current_reversal_exit`).

## Decisions: removed, rejected, not taken

- **Removed** (Oct 28, unused in 0.53.10 or covered): `stores_index_cases` (the fold `stores` with values per case),
  `select_store_other` (decided by `Simplify.select`), `perm_swaps_one`, `perm_steps`, `perm_steps_two`,
  `stores_cases_point`, `trace_merge_cases_ne` (by `stores_where` and `stores` with values per case),
  `invs_not_or` (by `sums`), the conditional-store lemmas (by `stores_where`), `select_current_trace_prefix_sums(_add)`
  (by `scans`), `select_current_trace_copy_both_ends(_list)` (by `copies`), `current_trace_two_phases`,
  `invs_two_phases`, `current_trace_increasing` (by `phases` and `sums`), the shape lemmas of the strided stores (by
  `strides₂` to `strides₅`), `sum_cases_below` (by `sum_above`, `sum_below`).
- **Removed** (Oct 26): `store_occurs_selects`, a forward lemma at the reads of every store whose instance, a
  disjunction no rule normalizes, came back at every firing (bugs.md; doc/teq.md, "What a forward lemma costs");
  replaced by `invs_select_store_ne`, a rule on the iteration constraint of the search (standard_sentinel-2, array_4).
- **Kept**: `store_select_other` (the equation of two arrays is not decided without it); `sum_indicator_true` and
  `_false` (a general `sum_cases_two` rewrites the sum before `sum_below` sees its comparison, brs2-brs5 lost).
- **Rejected**: a choice as a forward fact `current(T) == x0 || occurs(current(T), xs)` for a value that takes an
  element where a guard holds and keeps its value otherwise: the pattern also matches updates without a choice (the
  guard instantiated to true), and rewriting with the disjunctions of their instances does not terminate. The forward
  lemmas `div_mod` and `mod2_succ`: they trigger at every division and remainder; division and parity are in the
  arithmetic of `-prove` since 0.52.15.
- **Not taken**: the bounds by `max` and `min` through membership (no task needs it); one parity fact for the
  triangles (`triangle_even_scaled` does not cover `triangle_even` with `a = 1`, literal coefficients are not
  matched); converting the general fold `stores_where` into the compaction folds by lemmas (simpler by decision).

## Open points

- Usage annotations: the `(from ...)` lines and module headers are updated from the `:used` lists of the cloud runs;
  last on Oct 28 from 0.53.10.
- Lean: the index premises as `requires` where `-prove` decides them (TODO.md, "Proofs of teq.dfy in Lean").
- The matcher items of TODO.md ("Matching and rewriting"): conjunctions in order, literal disjunctive guards,
  higher-order variables for array reads, polymorphic higher-order side conditions, the selection of dependencies
  not backtracked, bare bound variables in `invs` patterns.
- The cancellation of constant offsets in sums (0.53.1) applies to all rules; the tasks whose rules match differently
  since are found by `scripts/missing.py` on the cloud logs.
