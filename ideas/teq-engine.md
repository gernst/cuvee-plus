# The engine: matcher, simplifier, diagnostics

Consolidated on Oct 12, 2026 from the findings of [examples/dafny/algorithms/NOTES.md](../examples/dafny/algorithms/NOTES.md)
(numbered there), the experiment threads of `pending/`, the principles section of
[doc/array-algorithms](../doc/array-algorithms), and the earlier ideas on binary search. Each item is a
workaround that every lemma written for a program carries today; ordered by expected payoff within each group.
None is implemented. The observations behind them are in TODO.md.

## Matching

1. **A re-entrance guard.** `Rewrite.conditions` simplifies the instance of a side condition before it decides
   or matches it, so a condition that mentions the rule's own left-hand side term (`l == current(Lv)` for a rule
   on `current(Lv)`) rewrites it by the rule itself and never terminates. Disable the rule, or do not rewrite the
   instance, while its conditions are evaluated. Unblocks the sound lower bound (`pending/lower_bound/lb_cmp4`),
   removes the `current(results(...))` detour of every summary, and admits conditions on the rule's own term in
   general. Smallest change, largest effect.
2. **Closed `invs` conditions matched, not decided.** A side condition whose variables are all bound is decided
   by the simplifier, which does not find a closed `invs` among the facts: these carry unused dependencies, which
   the simplifier also drops from the instance, and their bound variables are renamed. Match closed `invs`
   conditions against the facts modulo unused dependencies and α-renaming, like open ones. Removes the
   fresh-variable-plus-identifying-equation pattern from five files and shrinks the summaries by a third.
3. **A left-hand side matched through a trace variable's definition binds all its variables.**
   `current(trace(0, for ⌊counter(0, 1, nn)⌋, hs do ...))` against `current(Lo)` with `Lo == trace(...)` in the
   context binds the higher-order guard but leaves `nn` and `hs` unbound; the rule then fires with "variables of
   a rule not instantiated by its match", an error that replaces the goal, or its identifying equations stay
   open (finding 32). Bind them, or refuse the match. Also: the error should not replace the goal; a run with zero
   goals and an error looks like a proof.
4. **Literal patterns that are never matched, and the pin.** The matcher does not match: a literal step `-1` of a
   counter in a dependency pattern (it matches `counter(i, -1, n)` as a term), a disjunctive guard, arithmetic on
   a bound variable (`j - 1` as a store index, `n - k - 1` as a length, `natural(len - k - 1)`), a sum `m + n` of
   two rule variables, a higher-order summand `X(k) + integer(nn)` against a single summand, and a higher-order
   variable for a bare array read `G(i)` against `a[i]`, which is instantiated by the array (finding 10). The
   workaround is the pin: a higher-order variable `P(i)` or a variable `d` and a condition `forall i :: P(i) == i - 1`,
   `d == -1`, decided by beta reduction afterwards. The engine could do this itself: when a subterm of the
   pattern over bound variables does not match syntactically, abstract it as a fresh higher-order variable and
   decide the equation after the match (matching modulo the pin). This would close the recurrence lemmas on
   `a[k - 1]` of TODO.md as well. The downward stores-ahead lemma of the MonoCera tests needed exactly two pins.
5. **Bare bound variables are synthesized as maps.** An `invs` left-hand side with a bare bound variable of a
   variable dependency on one side (`n <= j`, `j == integer(nn)`) matches every comparison, respectively
   equation, fragment, with the dependency synthesized (`Rewrite.instantiate`), and with an `invs` side
   condition it cycles (findings 15, 29). Either restrict the synthesis to higher-order variables, or let
   `Rule.check` warn about such left-hand sides with `invs` conditions (a lint: `j == integer(nn)` cycles too,
   so no exact criterion).
6. **No backtracking over the selection of dependencies** when a side condition fails (finding 1,
   `invs_current_counter_other` exists only for this), and **equal counters `K == I` of one loop are not
   identified**, so the simplifier keeps both and patterns select among them.
7. **Rule variables are not renamed apart from the goal's.** A method variable named like a rule variable of an
   open condition makes the condition coincide with the fact literally; it is decided true without binding the
   variable (finding 9, 21). Rename apart before matching.
8. **Side conditions in the normal form of the included modules.** A summary is written for the fragment forms
   that the whole database produces (`j == current(J)` without `teq:nested`, `j == integer(nn) + k + 1` with it,
   finding 22). Unavoidable with ordered rewriting; e-graphs (equality saturation) would make the order and the
   orientation of equations moot, and are the principled answer to this and to item 12.
9. **Polymorphic lemmas with a higher-order variable in a side condition are not matched** (finding 4), hence
   monomorphic copies (`current_results_steps` for `int` and for arrays of arrays).
10. **A beta-redex is left in the output** after a higher-order variable is instantiated,
    `((k: int) => !nodup(a, k, n))(k)` (first_duplicate).

## The simplifier and its context

11. **Iteration constraints as side conditions cycle** by one mechanism: deciding an open `invs` condition
    builds the context of each `invs` fact's combinator and rewrites the reads `earlier(natural(k), ⌊X⌋)` there;
    if the rule's left-hand side matches a rewritten read, it recurs one level deeper until the step budget is
    exhausted. The convention is definitional atoms (`consts_prefix_def`); the engine could detect the
    re-entrance on the same term (item 1 again) instead of exhausting the budget, and report the cycle with the
    rule rather than the last step of the loop (`integer_natural` was reported for the nested module's cycle).
12. **Solutions of arithmetic equations are inlined into polynomials only**, not into function arguments: the
    exit `n == n' + 1` is not substituted into `sorted(a, 0, n)` (is_sorted, the one goal left), nor `n == C / 2`
    into `2 n <= i < C` (`half_even` of the MonoCera tests works around it). The orientation of equations in the
    context (`Chains.solve` picks a variable) and equations between `earlier` terms are the same problem: a
    congruence closure over the context would replace `replace/chain/solved/rules` and their interplay.
13. **Bounds that are no difference constraints** are not combined: `len <= 2 m + 1` from `n <= m + lo + 1` and
    `lo == m` (finding 28); `i == 0` from `0 <= i` and `!(1 <= i)` (finding 11); division has no bounds
    (`l <= (h + l) / 2`, `x / c <= 0`, `0 <= (n + n²) / 2`); products are not cancelled (`mul_eq_cancel`).
14. **Definition lemmas fire before the reads they hide are resolved.** `above_iterations_def` abstracts the
    checking loop's constraint `k <= a[k]` of `rewnifrev` into an atom before any lemma resolves `a[k]`, hiding
    the fact; in `rewnif` the read was resolved first. Definition lemmas should come after the reads of their
    bodies are rewritten (a priority, or a second pass), or match only bodies without unresolved reads of
    traces.
15. **The exit of an outer loop** is a disjunction in the conclusion, `i < n && !r || post`, which `-split` does
    not split and whose literals the context of `post` does not see (finding 31; first_duplicate states its
    postcondition as two implications). Split a disjunctive negated exit into one goal per literal. The case of
    no iteration appears only after a first simplification, hence `-simplify -split -simplify` (is_sorted,
    reverse); `-split` could iterate with `-simplify`.
16. **Nested loops in the simplifier itself.** The two minimal problems remain
    (`invs_counter_equation.dfy`, `invs_fragments.dfy`): the equation of a bound variable is not followed in the
    body of a sibling conjunct, and the fragments of an inner loop do not share facts. Sharing all `invs` over the
    same counter pointwise was implemented and reverted (it made rewriting cycle); the module `nested` does it by
    rewriting. The better fix, the paper's own remark in section 5: extend the dependency list of the combinator
    by the shared sequences with fresh bound variables instead of `earlier(k, Z)` reads, which keeps the binding
    structure. The best: simplify the trace equation system of the inner loop as a unit when symbolic execution
    summarizes it (interleave generation and rewriting), so that the outer body sees `j == n` or
    `b' == current(bubble_pass(b, ⌊counter(0, 1, i - 1)⌋))` directly; then the outer traces have summarized
    traces as updates, and the database needs lemmas over traces of passes.
17. **Facts about terms that occur** (the binary search, the partial descriptions): the rewriter only rewrites
    the goal and never adds facts, so bounds of `current(incs(...))` reach the goal only through a cut
    `assert φ; assume φ`. Forward rules triggered by terms, E-matching style with the rule's variables bound by
    the trigger, and the difference constraints of the context then derive the contradiction
    ([binary-search.md](binary-search.md), [doc/simplifier.md](../doc/simplifier.md#forward-reasoning)).
    The `forward` branch has a version; `Simplify.nary` re-deriving the same conclusions in every sibling
    context made it slow.
18. **Conditional stores instead of cases**: a body with `s` conditional stores at the same positions becomes
    `2^s` cases, which no lemma with a fixed number of cases covers (`pr3`-`pr5`), and sequences of ten
    conditionals overflow the stack. Merge in `-teq` (a conditional whose branches store at the same index as one
    store of a conditional value) or as a normalization of `Eps`; see [conditional-stores.md](conditional-stores.md).
19. **Quantified left-hand sides and witnesses.** A rule whose left-hand side is a quantifier is never tried,
    and `-teq` produces no witness for `exists k :: a[k] == m` (max_element); quantified hypotheses are matched by
    no side condition (counting_sort uses an atom). Either quantified patterns in the rewriter, or a witness
    trace named by the program (argmax keeps the position).

## Diagnostics and robustness

20. **`-probe <lemma>`**: report the first side condition of a named rule that fails on a goal, with the facts it
    was matched against, and which part of a left-hand side did not match. The truncated copies, probe rules and
    pair runs of `pending/` took an afternoon each for information the engine has; the rewnifrev diagnosis of
    Oct 12 took five runs.
21. **A killed run prints no goal.** A timeout should report the goal it was working on, so that a runner never
    counts a kill as a proof (finding 18, twice in one week).
22. **A lemma of an injected module does not fire where the identical lemma in the input does**
    (`invs_counter_consts` on row_sums, finding 34; `-rules` does not list it). Not understood; the rules differ
    by the attribute `{:teq}` and by their position. Also finding 12, a summary that fired in exactly one run:
    an order that depends on an unordered collection somewhere.
23. **Eta reduction of lambdas of array type** turned `(z) => a[z]` into `a`, leaving `a(k)` (fixed in 0.35.15);
    the same phenomenon in the matcher is item 4.

## Cheap extensions of the method

24. **Bug finding by small `n`.** Trace equation systems are complete, so an unsafe task is witnessed by a small
    number of iterations: instantiate `n = 0, 1, 2`, the sequences become tuples and the goal is
    quantifier-free. Covers the unsafe half of SV-COMP at BMC cost; today only `-chc` refutes.
25. **Termination** by a bound on `steps(K)` from the iteration constraints.
26. **Procedures**: inline only today; a trace of calls, or contracts as lemmas about a named summary function.
