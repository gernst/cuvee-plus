# Review of the lemma database (Oct 23, 2026)

A pass over teq.dfy and the modules of [resources/cuvee/teq](../resources/cuvee/teq): which lemmas the proved tasks
of SV-COMP use, what could be unified, which lemmas work around gaps of the engine of `-prove`, and the open points
of earlier analyses. Usage is the union of the results of Cuvée and Cuvée+Z3 since Oct 13, 2026 (70 result files,
counted by `-rules` as in [scripts/rules.py](../scripts/rules.py)); MonoCera and the examples are not counted.

## Done

- `consts_prefix`, `consts_prefix_def`, `sum_consts_prefix` dropped (to the legacy file, then removed with it): `consts_choice` and `sum_consts`
  cover them, and the length premise of `sum_consts_prefix` is gone from lean/premises.txt.
- `mods` is a fold (`{:fold}` with the trace of its update), `mods_def` gone; the Lean proofs go through
  `mods_start` (the trace over a counter of any start is the same).
- Renamed, since they rewrite into a function without defining it: `counts_false`, `counts_true` (traces of
  booleans), `stores_cases`, `stores_index_cases`, `stores_read_unmodified`, `sorted_adjacent`, `not_occurs_prefix`,
  `not_occurs_selects`. `counter_def`, `consts_def`, `agree_prefix_def`, `above_iterations_def` keep the suffix,
  see below.
- One counter instead of two: the eight lemmas that iterated over `⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k,
  i` of the per-variable form iterate over `⌊counter(0, 1, n)⌋ do a, k` (arrays: `stores_cases`,
  `stores_index_cases`, `select_current_trace_reset_keep`, `select_current_trace_conditional_store`; strides:
  `stride2`, `stride3`, `ahead`; aggregation: `select_current_trace_reset_add`); in Lean, each is derived from its
  former statement (`<name>_zip`) by `trace_zip_self`.
- `count_false_below` and `count_false_above` dropped: `count_false_true` reduces a count of false to
  the count of true, which `count_true_below`/`_above` evaluate.
- One prefix for the reads of a final array: `select_current_trace_conditional_store(_deps)`,
  `select_current_trace_cap`, `select_current_trace_prefix_sums(_add)`.
- `select_current_trace_stride2_cases` over one counter: its second counter, `⌊counter(1, 1, n)⌋`, was not read.
- From examples/dafny/algorithms: `current_trace_flag` of counters.dfy is of any type (it replaces the boolean copy
  of is_sorted.dfy), and `current_trace_histogram` (counting_sort.dfy) is in aggregation.dfy; both proved in Lean.
- `pow_two_mod_three` dropped, local again in underapprox_1-2 of the former Dafny translations of SV-COMP (removed Oct 23, 2026), with
  `current_trace_geometric`, which it needs too.
- The TODOs in the modules are gone: `cut` and `sorted` keep their integer bounds, those of the programs (a natural
  length would add conversions without simplifying a proof); `cutFrom` stays the recursion on a natural for Lean;
  the arrays TODOs are answered in [conditional-stores.md](conditional-stores.md) (the missing join of guarded
  stores, and constant abstractions); a `swap` fold for the permutations remains an idea (below).
- `swap(a, p, q)` is a fold of its two stores in sorted.dfy (formerly a TODO there), with `select_swap` for its
  elements; `perm_swap`, `perm_swaps_one`, `perm_swaps` are stated over it, so `P` and `Q` occur once each. The six
  sorting examples that include `teq:sorted` state their local swaps as `swap(...)`, since the stores of the
  programs are folded before their lemmas are matched (without that, two leave a goal, three time out, one does not
  terminate); all ten examples with `teq:sorted` are correct with it; SV-COMP not run yet.
- The legacy database is removed (resources/cuvee/legacy: the former single file of the per-variable form,
  core.dfy, the retired `nested`), with the 60 theorems of Proofs.lean that only its lemmas needed, their auxiliary
  predicates (`below_prefix`, `nonneg_prefix`, `consts_prefix`) and lemmas, and their counterexamples; four of its
  theorems stay as auxiliary lemmas of kept proofs (`earlier_prefix`, `natural_zero`, `selects_stores`,
  `select_not_occurs_selects_beyond`). The unit tests of test/dafny/TEQ.scala parse the modules instead (the
  assertion on the selects of a store, a rule of the legacy file only, is gone). fragments.dfy of the algorithms,
  the fragment lemmas of the former `nested`, is removed.
- `hs` dropped from the seven lemmas whose body does not read it (`count_remainder`, `select_current_trace_cap`,
  `current_trace_mod_add_const`, `current_trace_mod_add_cases`, `agree_prefix_def`, `not_occurs_prefix`,
  `above_iterations_def`): the matcher ignores the dependencies of the expression that the pattern does not select,
  and on the 21 tasks that use six of them (8 of the 27 of `not_occurs_prefix`), the outputs were byte-identical with
  and without `hs`. It stays where the body reads it through a higher-order variable (table below). The Lean proofs
  are direct over the counter.
- New in the database, proved in Lean: `indexof_counter_step` (the position in a counter with a step, beside
  `occurs_counter_step`), `selects_nil`, `perm_steps_nat` and `perm_steps_three` (the copies of bubble_sort, the insertion sorts and
  selection_sort; one lemma per number and type of dependencies, see the table below). argmax.dfy iterates over one
  counter.
- `butlast_counter_zero` (`⌊counter(i, c, zero)⌋ == nil`, added for prefix_sums.dfy) dropped again: it turned the
  counter of an inner loop without iterations into `nil`, on which no rule acts, where the lemmas on counters had
  closed the goal (nested3-2, bugs.md, Fixed).
- `integer_natural_facts`, a forward lemma `0 <= integer(n) && natural(integer(n)) == n` at every `integer(n)` beside
  `integer_eq` (bcbef0d3), was dropped again: it kept everything on reverse, nested_sum, while_infinite_loop_4 (25 s
  to 13 s), const_1-1, in-de20 and cohencu-ll_valuebound5, but cost time wherever `integer(n)` occurs, since forward
  instances are simplified again at every fact; MonoCera lost 8 tasks at 60 s (s1lif and condn time out at 120 s with
  it, prove in 14 s and 21 s without; bugs.md, Fixed). Of the other variants, the forward lemma instead of `integer_eq`
  loses nested_sum (`integer_eq` works in the bodies of iteration constraints, which forward lemmas do not reach) and
  the unconditional `integer_eq` changed nothing measured; `integer_eq` stays as it is.
- `agree_prefix` and `above_iterations` are folds of their iteration constraints (`agree_prefix_def`,
  `above_iterations_def` gone); in Lean, their characterizations are proved from the definitions by `invs`, and
  `earlier_above_iterations` has the length premise of `ts` in lean/premises.txt, since the printer does not see that
  `ts` is a dependency through the fold. The nine tasks of the two former lemmas answer as before.
- `mill -i test` checks that the generated Lean statements are those of the current modules
  (test/src/cuvee/test/Lean.scala, `generate.py --check --classpath` of the tests).
- The local copies of `perm_steps` are gone from bubble_sort, insertion_sort, insertion_sort2 and selection_sort,
  which use `perm_steps_nat` and `perm_steps_three` of `teq:sorted` (all four correct, 22 to 33 s).
- examples/dafny/algorithms/NOTES.md is replaced by [doc/algorithms.md](../doc/algorithms.md): the status of all 30
  examples from a run of 0.50.8, how they are proved, the principles for their lemmas under `-prove`, and a history
  section that points to the last version of NOTES.md for the numbered findings of Oct 9 to 16.
- Each lemma that at most three proved tasks use names them on its `(from ...)` line, each unused lemma says why it
  stays (doc/teq.md, conventions); stale remarks fixed (rewnifrev is proved by `select_current_trace_ahead_down`,
  `integer_zero` is in teq.dfy).

## Usage

121 of the 150 lemmas and folds were used (before the unifications). Unused: the module `sorted` (the examples only), the bisection of `search`
(`bisection`, `bisection_lo/hi`), `earlier_above_iterations`, `div_nonpos`, `pow_two_mod_three`, `prefix_sums`,
`sum_empty`, `sum_indicator_false`, `count_false_above` (dropped), `parities` with `current_parities`,
`select_current_trace_prefix_sums_add`. Of these, only `pow_two_mod_three` is specific to the constants of its tasks (a
dropped); the others are laws of functions of the database or pairs of used lemmas. 41
lemmas are used by at most three tasks.

## What could be unified (database only)

Done on Oct 23, 2026 (above): the duplicated counters, the counts of a threshold, the names of the reads. Open:

- **Membership in a counter.** `occurs_counter_up` (178 tasks) is `occurs_counter_step` at step 1; keep both (the
  remainder `(j - i) % 1` would have to simplify first), but `indexof_counter_up` has no general version.
- **Disjunction-free variants** (`invs_counter_upper_nonnegative` beside `invs_counter_upper`, `invs_mods_upper`
  beside `_cases`, `invs_mods_down` beside `_cases`, `invs_counter_mod_upper_zero` beside `_cases`): each pair is a
  specialization whose side condition removes the disjunction `n == zero || ...`, which is not split in the context
  of a combinator; they stay as long as that holds (see below).
- `sum_indicator_false` stays: it turns a sum into a count, which `count_false_true` does not do.
- **Folds that are not possible.** `counter_def` (the counter is the dependency of its own trace; a fold body would
  mention `counter`), `consts_def` (over a counter of any start and step, while a fold abstracts its formals only;
  a fold over `⌊counter(0, 1, n)⌋` would lose the general form).

## The lemmas of examples/dafny/algorithms

Seven examples of examples/dafny/state duplicated programs of examples/dafny/algorithms with the database alone
(nested_counter, nested_sum, nested_mult, row_sums, transpose, lsearch, lower_bound); they replaced the versions with
local lemmas there (Oct 23, 2026), which removed the fragment lemmas of the former module `nested`, `results`,
`mul_eq_cancel` and the local copies of the search lemmas; examples/dafny/teq/lsearch.dfy, a third copy, is gone.
Of the other local lemmas:

- **Copies of the database**, removed: perm.dfy (`perm_refl`, `perm_swap`, `perm_swaps`, with `teq:sorted`),
  is_sorted.dfy (`sorted_def`, `sorted_short`, and the boolean `current_trace_flag_bool`, with `teq:sorted` and
  `teq:counters`); bubble_sort, gnome_sort, insertion_sort, insertion_sort2, selection_sort, partition
  (`sorted`, `perm`, `partitioned`, `perm_refl`, with `teq:sorted`, Oct 23, 2026: correct as before, 30 to 80 %
  slower, since the other rules of the module are tried too). Left: cocktail_sort (also a copy of `perm_steps`),
  three_way_partition, merge, counting_sort, which time out at 60 s with and without the copies, so the switch could
  not be compared.
- **Moved into the database**: `current_trace_flag` of any type, `current_trace_histogram`.
- **Candidates, not moved**: the bounds of `maxs` over `selects` (`select_le_maxs`, `occurs_maxs` of max_element,
  which stays open for its existential postcondition); the fold `argmaxs` with its bounds (argmax.dfy, over one counter
  since Oct 23, 2026); `invs_pairs` of reverse.dfy as an affine bound
  `a k + b < m` of a counter; `perm_steps` with three dependencies or a natural one (`perm_steps_three`,
  `perm_steps_choice`), now in the database as `perm_steps_nat` and `perm_steps_three` (Done above); `sum_selects_zero` (prefix_sums.dfy), better as `⌊counter(i, c, zero)⌋ == nil`. None of them
  occurs in the SV-COMP translations.
- **Specific to their programs**, staying local: the folds and inductions of the sorting algorithms (`bubble_pass`,
  `insert_pass`, `shake`, `lomuto`, `threeway`, `bubbled`, ...), merge (`merged`), counting_sort (`rank_table`,
  the scatter), distinct and first_duplicate (`nodup`, `scan`), transpose, reverse (`current_reversal_exit`), and
  fragments.dfy (the fragment lemmas of the former module `nested`, an example of their own).

## Workarounds for gaps of the engine

Lemmas or shapes of lemmas that exist because the matcher or the engine of `-prove` lacks something; each could go
once the gap is closed (Scala changes, not done here).

| Gap | Lemmas |
|---|---|
| a higher-order instance must contain the term it abstracts (`Rewrite.abstraction`): no constant functions | `stores_cases` (its first case stores a constant `c`), the conditional-store family below |
| no join of guarded stores into a store of a conditional value (a pattern with two cases also matches one case) | `stores_cases`, `stores_index_cases`, `select_current_trace_conditional_store(_deps)`, `select_current_trace_cap`, `select_current_trace_reset_keep`, `select_current_trace_stride2_cases` (and the 2^s cases of pr3-pr5, [conditional-stores.md](conditional-stores.md)) |
| a sum pattern `a + b * v` gives no variable the empty sum 0 | `maps_counter_scale` beside `maps_counter_affine` |
| a higher-order summand takes a single summand | `select_current_trace_prefix_sums_add` beside `select_current_trace_prefix_sums` |
| literals in patterns: `-1` is not matched, nor a coefficient by a variable | `select_current_trace_ahead_down` (`i + (-1)`), `mul_lt_cancel` (no literal coefficient), reverse.dfy (step as a variable) |
| a term `F(c)` in a result is compared literally | `trace_merge_cases_ne` (result `d` with `d == F(c)` as a side condition) |
| guards on booleans are not identified with `b == true` | `counts_false`, `counts_true` (order: false first) |
| the disjunction `n == zero || ...` is not split in the context of a combinator | the disjunction-free variants above |
| facts of the classes (`n == zero`, `n == natural(x)`) do not reach the linear arithmetic | `zero_integer_value`, `natural_positive` (forward lemmas), `integer_eq` with its side condition (TODO.md) |
| an iteration constraint as a side condition recurs through its own fact | atoms for constraints: `agree_prefix`, `above_iterations`, `!occurs(e, prefix(...))` |
| a rule variable must not capture a bound variable of the expression | the further dependency `hs` of the lemmas whose body reads it through a higher-order variable, `D(k, h)` (`current_trace_flag`, `current_trace_increasing`, `count_false_true`, `count_true_eq`, `stores_read_unmodified`, `select_current_trace_conditional_store_deps`) |
| an equation of integers as a lemma rewrites its left-hand side as a term | `double_eq_half` (stated as an equivalence of atoms) |
| complete guards are an obligation of the proofs | the complementary last case of `current_trace_increasing`, `current_trace_bounded`, `bisection` |
| the engine does not check reads within the loop or lengths | the premises of [lean/premises.txt](../lean/premises.txt) |
| a pattern of nested stores has a fixed number of stores | the stride lemmas (2, 3, the cases of pr2) |
| a pattern has a fixed number of dependencies, one bound variable each (no tuples), and a polymorphic higher-order side condition is not matched | one lemma per number and type of dependencies: `perm_steps` (int), `perm_steps_two` (int, int), `perm_steps_nat` (int, Nat), `perm_steps_three` (int, Nat, int), where Lean proves all from one lemma over any list of dependencies (`perm_steps_general`); kept specific by decision (Oct 23, 2026) |

## Open points of earlier analyses

- The normal form of naturals and integers: `integer_eq` loses `0 <= x` and moves the equation out of the
  arithmetic (TODO.md, reverse.dfy); options: the unconditional form, a forward lemma that keeps the equation, or a
  bridge from the classes to the arithmetic (Scala).
- Lean (TODO.md, Proofs of teq.dfy in Lean): the index premises as `requires` where `-prove` decides them.
- The benchmark definitions include all modules, the options in fm-tools do not (TODO.md).
- The matcher items of TODO.md (Simplifier and rewriting) were found under `-simplify` and are to be rechecked under
  `-prove`: products modulo commutativity (`div_quotient_remainder`, dropped), conjunctions in order,
  literal disjunctive guards, higher-order variables for array reads, polymorphic higher-order side conditions,
  the selection of dependencies not backtracked, bare bound variables in `invs` patterns.
