# Guards in disjunctive normal form

A proposal for the normal form of the cases of updates (`Eps`): one case per conjunction of tests, with the merging
of cases by their results moved from the simplifier into the matcher. Prerequisite: the conditionals of the results
of traces are lifted into cases (`Simplify.cases`, 0.52.7), which produces such conjunctions anyway.

## Now

`Simplify.eps` merges cases with equal results by the disjunction of their guards, and a single case is its result:
`case b => y case c => y` is `y`. Lifting a conditional `ite(c, a, b)` out of a result gives cases `c` and `!c`,
nested lifts conjunctions `c && d`, `c && !d`, ...; merging reintroduces disjunctions such as `(c && d) || !c`.
Since 0.52.11, `TEQ.update` groups the paths of a loop body by their results already, before any simplification
(examples/c/teq/stores_cases_point.c is proved without a lemma by it), and a single guarded case stays a choice there
(0.52.12, ideas/engine-gaps.md, 3c). Only cases with equal results are merged, by decision (Oct 27): merging cases with
different results by conditional values (`Simplify.eps`, chains of stores) lost tasks and was withdrawn
(ideas/conditional-stores.md). Since 0.52.17, a side condition that does not simplify to true is tried once more with
its choices lifted out of its atoms (`Normalize.choices`), a disjunctive view of the cases on demand, which keeps them.

Disjunctive guards of expressions are a gap of the matcher (TODO.md, "Trace equation systems": literal disjunctive
guards matched only through a higher-order variable pinned by a quantified side condition, merge, insertion_sort,
cocktail_sort): a pattern case with a concrete guard covers an expression case only if the guard of the expression
implies it, and a disjunction implies it only if every disjunct does, which the check does not see through the
merged form.

## Proposal

- The guards of `Eps` are conjunctions of literals (tests and their negations), disjoint as now: a test `a || b` of a
  branch becomes the cases `a` and `!a && b`, not two overlapping cases; `Eps.flatten` already conjoins the guards of
  nested choices.
- Cases with equal results stay apart. A choice whose results are all equal is still its result, since a trace that
  keeps its value must be `y` for `consts_def` and the lemmas on traces that keep their value.
- Each result is simplified under its own conjunction, which is more precise than under the disjunction.

## The matcher

The coverage check needs no change for concrete pattern guards: each case of the expression must be covered by a case
of the pattern whose guard follows from the guard of the expression, so one pattern case `m < v => v` covers the
expression cases `m < v && P => v` and `m < v && !P => v`. Pattern guards written as disjunctions, e.g. the third case
of `bisection` in search.dfy, still cover DNF cases, since the direction is from the expression to the pattern.

Higher-order guard variables need the merging: in `case C(k) => a[k := V(k)] case !C(k) => a`
(select_current_trace_conditional_store, stores_cases, counts), `C` is bound from the first case of the expression.
A program `if (c1) a[k] = v; else if (c2) a[k] = v;` has the DNF cases `c1`, `!c1 && c2` with the same result and
`!c1 && !c2` keeping the array; `C` binds to `c1`, and the second case does not follow from it. Hence:

- when a pattern case whose guard is a higher-order variable applied to bound variables is matched, the matcher
  groups the expression cases whose results match its result under the same instantiation of the other variables,
  and binds the variable to the disjunction of their guards (`C := c1 || !c1 && c2`, simplified to `c1 || c2`);
- the complementary pattern case `!C(k)` then covers the remaining cases, whose guards imply the negation.

That is the merging of `Simplify.eps`, done on demand where a pattern needs it, instead of in the normal form for
all.

## Risks

- Size: DNF can be exponential in nested and sequenced conditionals, which `-teq` already is (bugs.md, the overflow
  at ten conditionals; ideas/conditional-stores.md). The merging now keeps some of these small, e.g. two branches
  that store the same value.
- Lemmas written against merged guards (e.g. `trace_merge_cases_ne` in counters.dfy, the guards of the third case of
  `bisection`) are to be checked against the new form; `scripts/missing.py` on a run before and after finds the
  rules that no longer apply.
- Results that are equal only modulo the guard (`k != c => a[k := F(k)]`, `k == c => a[c := F(c)]`, copysome2-1)
  are merged since 0.53.3 by `Simplify.eps` under guards with an equation (doc/prove.md); the grouping of the matcher
  would do the same.

## Steps

1. Done: the lifting of conditionals was adopted in 0.52.7; it split the addition of the reset-add loop of
   brs2-brs5, recovered by a lemma in 0.52.17 (`select_current_trace_reset_add_keep`).
2. Drop the merging by results in `Simplify.eps` and the grouping of `TEQ.update` (0.52.11), except for a choice
   whose results are all equal; split disjunctive tests of branches into disjoint conjunctions.
3. The grouping of cases for higher-order guard variables in `Rewrite`.
4. Rerun, compare with `scripts/compare.py`, find lost rules with `scripts/missing.py`.
