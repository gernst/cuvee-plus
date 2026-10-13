# The lemma database: modules, schemas, coverage

Consolidated on Oct 12, 2026 from the findings and proposals of
[examples/dafny/algorithms/NOTES.md](../examples/dafny/algorithms/NOTES.md), the experiment threads of
`pending/`, [benchmarks/monocera/summary.md](../benchmarks/monocera/summary.md), and the principles section of
[doc/array-algorithms](../doc/array-algorithms). The engine items that the lemmas work around are in
[teq-engine.md](teq-engine.md).

## Ready to land

1. **The module `nested` into `-teq`.** With the summaries of the insertion sorts and the cocktail sort restated
   for its fragment forms, all 30 algorithms agree with their expected goals with the module included and nothing
   cycles (finding 37). Remaining: the entry in `TEQ.modules`, a run on the SV-COMP translations, and the removal
   of the duplicate lemmas from the example files.
2. **`select_current_trace_ahead_down` restated** with the step of the counter as a variable `d` with `d == -1`
   as a side condition and the position `i - 1` as a pinned higher-order variable: closes `forall/rewnifrev` and
   `min/rewnifrev` of the MonoCera tests (the wrong assertion leaves a goal), checked on Oct 12
   (`doc/array-algorithms`, the stores-ahead section). `rewnifrev2` stores ahead upwards in a downward loop, a
   third shape.
3. **The chain lemmas of row_sums into `nested`**, generalized: counters over constant numbers of iterations
   (there), final values of inner traces given per iteration, pointwise definitions as `maps`, reads of a `maps`
   over the counter (finding 30). Blocked by finding 34 (a module lemma that fires from the input and not from
   the module), to be understood first.
4. **The module `sorting` taken up by the examples**, which duplicate its lemmas locally; no file includes it yet.

## Soundness of what is trusted

5. **Lean proofs for `nested`, `sorting`, `strides`.** The core modules are proved (164 of 205 lemmas); these
   three are not, and `strides` fixes the number of stores and cases on its left-hand sides. The restated exit
   lemma and `invs_natural_consts` are small.
6. **Definitions for the abstract predicates.** `sorted`, `perm`, `partitioned`, `bubbled`, `shaken`, `argmin`,
   `insert`, `shake`, `nodup`, `merged`, `lb` are axiomatized by their lemmas; nothing checks the step lemmas or
   the summaries, which state an inner loop's correctness in one line. A Lean model with definitions would make
   them provable, and the user lemmas of a program are the next thing that needs a proof route
   ([trace-lemma-proofs.md](trace-lemma-proofs.md)).
7. **Well-formedness premises explicit** (bugs.md): equal lengths of dependencies, indices in range, complete
   guards, which the Lean proofs needed and the statements omit; the fallback encoding does not assume them, a
   candidate cause of its wrong proofs.
8. **Every summary checked on a wrong postcondition**, as a rule of the folder; two vacuous proofs occurred (a
   side condition simplified under the conclusion, finding 13; the duplicate-variable trick in the wrong
   direction). A harness that runs each `-teq` example with its `*_wrong` variant would make the check routine.

## Shape of the database

9. **Lemma schemas instead of lemma lists.** Most acceleration lemmas of a named scan
   `g(x0, V) = trace(x0, for V do x, v :: f(x, v))` are instances of free theorems:
   `prefix(k, ⌊g(x0, V)⌋) = ⌊g(x0, prefix(k, V))⌋`, `earlier(j, ⌊g(x0, V)⌋) = current(g(x0, prefix(j, V)))`,
   `current(g(x0, V ++ ⟨v⟩)) = f(current(g(x0, V)), v)`, `g` over `map` commutes. One schema per observer with
   higher-order patterns replaces `prefix_sums`, `prefix_maxs`, `prefix_counts`, ...; the derivation of
   acceleration lemmas by fusion ([trace-lemma-proofs.md](trace-lemma-proofs.md)) is the mechanical form.
10. **Variadic patterns.** `perm_swaps_one`/`perm_swaps`, `perm_steps`/`perm_steps_two`,
    `sorted_prefix_steps`/`_two`, the strides 2 and 3, the stores-ahead up and down, and the monomorphic copies
    for arrays of arrays are arity and type variants of one lemma each; a pattern with the number of
    dependencies, the stride, or the number of cases as a parameter would fold them.
11. **Definition lemmas late, atoms for constraints.** An iteration constraint is never a side condition; a
    definition lemma abstracts it by an atom with a body the matcher cannot synthesize (an explicit read
    `earlier(natural(k), js) == c`), and the lemma that needs it takes the atom. The order of modules decides which
    abstraction a fragment gets (`consts_prefix_def` of `aggregation` before `nested`, hence
    `consts_prefix_integer`); definition lemmas should come after the lemmas that use the raw constraints, and
    after the reads in their bodies are resolved (engine item 14).
12. **Invariant schemes as lemmas** for the partial descriptions the paper names as its weakness: the induction
    `P(x0) ∧ (∀ x k. 0 ≤ k < n ∧ P(x, k) ⇒ P(F(x, k), k + 1)) ⇒ P(current(trace(...)), n)` with `P` an abstract
    predicate indexed by the iteration (`bubbled`, `shaken`, `sorted_prefix_steps`, the paper's
    `current_trace_bounded`), whose step the database proves by lemmas on atoms. Generic forms for bounds of
    monotone traces (`incs`, `decs`), minima and maxima under conditional updates, and the binary search
    ([binary-search.md](binary-search.md)); `P` taken from the atoms of the goal about `current(X)` is
    goal-directed generalization, the bridge to invariant inference with the database proving the steps.

## Coverage: the open shapes

13. **Recurrences on earlier entries with polynomial closed forms** (`ifeqn1`-`5`, `ifcomp`, `pcomp`, `sqm`,
    `nsqm`, `condm` of MonoCera; 72 of the 96 open goals of the earlier run are the checking loop's assertion at
    the current index of such an array): an introduction lemma that names `a[k] = a[k - 1] + c` from `a[0] = c`
    with the closed form `c (j + 1)`, sums of affine maps for `b[k] = b[k - 1] + a[k - 1]`, or a recurrence
    solver (compositional recurrence analysis, closed forms for numerical loops) as a lemma generator for the
    arithmetic fragment. Needs engine item 4 first: `k - 1` as a store index is not matched.
14. **Strides with per-cell cases** (`pr3`-`pr5`, `2^s` cases) and **writes by inner loops** (`nr*`): the former
    by conditional stores (engine item 18), the latter by the summaries of inner loops of the algorithms, which
    MonoCera's instrumentation handles and the module `nested` does not yet.
15. **Nondeterministic input arrays** (`standard_vararg_ground`, `sanfoundry_27_ground`, 40 goals): the
    constraint of one loop (`0 <= earlier(natural(k), Tmp?)`) instantiated at the index of another, and reads
    beyond the initialized prefix mixing `earlier` and `select`; the instantiation-at-a-witness pattern of the
    linear search, generalized.
16. **Closed forms with division** (`array_init_var_plus_ind*`, `j == k (k + 1) / 2`, the goal
    `0 <= (n + n²) div 2`): bounds of division in the simplifier (engine item 13).
17. **Nested loops with stored inner results beyond row sums**: inner results that are themselves traces
    (bubble passes), traces of passes with `sorted`/`perm`/`partitioned` facts per pass, once the engine
    summarizes inner loops as units (engine item 16).
18. **The remaining algorithms**: `is_sorted` (engine item 12), the `exists` of `max_element` (engine item 19),
    the lower bound (engine item 1), `rewnifrev2`.

## Hygiene

19. `half_even` stays outside the database as a workaround for engine item 12; `mul_eq_cancel`,
    `invs_current_counter_other` and the `_zero` variants exist only because of engine items 12, 6 and 8.
20. `teq.dfy` is the former single file, kept and not injected; it should be retired once nothing refers to it
    (the `(from ...)` comments and `Examples`), or regenerated from the modules.
21. The summary of the MonoCera tests says the literal `-1` was excluded as the cause of the rewnifrev
    failure; it was the cause in the dependency position (item 2). To be corrected there.
