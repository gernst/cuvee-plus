# Review of the lemma database

Open points of a pass over teq.dfy and the modules of [resources/cuvee/teq](../resources/cuvee/teq): what could be
unified, which local lemmas of the algorithms are candidates for the database, and which lemmas work around gaps of
the engine of `-prove`. Usage is counted by `-rules` over the results of Cuvée ([scripts/rules.py](../scripts/rules.py));
a lemma that at most three proved tasks use names them on its `(from ...)` line (doc/teq.md).

## What could be unified

- **Membership in a counter.** `occurs_counter_up` is `occurs_counter_step` at step 1; both stay (the remainder
  `(j - i) % 1` would have to simplify first), but `indexof_counter_up` has no general version.
- **Disjunction-free variants** (`invs_counter_upper_nonnegative` beside `invs_counter_upper`, `invs_mods_upper` and
  `invs_mods_down` beside their `_cases`, `invs_counter_mod_upper_zero` beside `_cases`): each is a specialization
  whose side condition removes the disjunction `n <= 0 || ...`, which is not split in the context of a combinator.
- **Folds that are not possible.** `counter_def` (the counter is the dependency of its own trace) and `consts_def`
  (over a counter of any start and step, while a fold abstracts its formals only).

## The lemmas of examples/dafny/algorithms

- **Candidates, not moved**: the bounds of `maxs` over `selects` (`select_le_maxs`, `occurs_maxs` of max_element); the
  fold `argmaxs` with its bounds (argmax.dfy); `invs_pairs` of reverse.dfy as an affine bound of a counter;
  `sum_selects_zero` (prefix_sums.dfy). None occurs in SV-COMP.
- **Copies left**: cocktail_sort, three_way_partition, merge, counting_sort copy predicates of `teq:sorted`; they time
  out with and without the copies.
- **Specific to their programs**, staying local: the folds and inductions of the sorting algorithms (`bubble_pass`,
  `insert_pass`, `shake`, `lomuto`, `threeway`, `bubbled`, ...), merge (`merged`), counting_sort (`rank_table`),
  distinct and first_duplicate (`nodup`, `scan`), transpose, reverse (`current_reversal_exit`).

## Workarounds for gaps of the engine

Lemmas or shapes of lemmas that exist because the matcher or the engine lacks something; each could go once the gap
is closed.

| Gap | Lemmas |
|---|---|
| a higher-order instance must contain the term it abstracts: no constant functions | `stores_cases` (its first case stores a constant), the conditional-store family below |
| no join of guarded stores into a store of a conditional value | `stores_cases`, `stores_index_cases`, `select_current_trace_conditional_store(_deps)`, `select_current_trace_cap`, `select_current_trace_reset_keep`, `select_current_trace_stride2_cases` ([conditional-stores.md](conditional-stores.md)) |
| a sum pattern `a + b * v` gives no variable the empty sum 0 | `maps_counter_scale` beside `maps_counter_affine` |
| a higher-order summand takes a single summand | `select_current_trace_prefix_sums_add` beside `select_current_trace_prefix_sums` |
| literals in patterns: `-1` is not matched, nor a coefficient by a variable | `select_current_trace_ahead_down`, `mul_lt_cancel`, reverse.dfy (step as a variable) |
| a term `F(c)` in a result is compared literally | `trace_merge_cases_ne` |
| guards on booleans are not identified with `b == true` | `counts_false`, `counts_true` (false first) |
| the disjunction `n <= 0 || ...` is not split in the context of a combinator | the disjunction-free variants above |
| an iteration constraint as a side condition recurs through its own fact | atoms for constraints: `agree_prefix`, `above_iterations`, `!occurs(e, prefix(...))` |
| a rule variable must not capture a bound variable of the expression | the dependency `hs` of lemmas whose body reads it through a higher-order variable `D(k, h)` (`current_trace_flag`, `current_trace_increasing`, `count_false_true`, `count_true_eq`, `stores_read_unmodified`, `select_current_trace_conditional_store_deps`) |
| an equation of integers as a lemma rewrites its left-hand side as a term | `double_eq_half` (an equivalence of atoms) |
| complete guards are an obligation of the proofs | the complementary last case of `current_trace_increasing`, `current_trace_bounded`, `bisection` |
| the engine does not check reads within the loop or lengths | the premises of [lean/premises.txt](../lean/premises.txt) |
| a pattern of nested stores has a fixed number of stores | the stride lemmas (2, 3, the cases of pr2) |
| a pattern has a fixed number of dependencies, one bound variable each, and a polymorphic higher-order side condition is not matched | one lemma per number of dependencies: `perm_steps`, `perm_steps_two`, `perm_steps_three`, which Lean proves from one lemma over any list of dependencies (`perm_steps_general`); kept specific by decision |

## Rejected lemmas

- A choice, as a forward fact `current(T) == x0 || occurs(current(T), xs)` for a value that takes an element where a
  guard holds and keeps its value otherwise: the pattern also matches updates without a choice (the guard
  instantiated to true), e.g. the copy of the bound of an unwinding, and rewriting with the disjunctions of their
  instances does not terminate. A pattern cannot exclude a guard that is constantly true.

## Open points

- Lean: the index premises as `requires` where `-prove` decides them (TODO.md).
- The benchmark definitions include all modules, the options in fm-tools do not (TODO.md).
- The matcher items of TODO.md ("Matching and rewriting"): conjunctions in order, literal disjunctive guards,
  higher-order variables for array reads, polymorphic higher-order side conditions, the selection of dependencies
  not backtracked, bare bound variables in `invs` patterns.
