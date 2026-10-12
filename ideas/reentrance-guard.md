# A re-entrance guard against cycles of conditional rules

Proposal of Oct 12, 2026, implemented the same day in 0.42.3 (see Result at the end).
Item 1 of [teq-engine.md](teq-engine.md); the observations are in TODO.md (the entry on `sum_invs_const`) and
in findings 19, 20, 24, 29 and 32 of [NOTES.md](../examples/dafny/algorithms/NOTES.md).

## The two issues

Both are the same rule applied again while its own side conditions are being evaluated, through two paths out
of `Rewrite.apply(rule)` ([Rewrite.scala](../src/cuvee/simplify/Rewrite.scala)):

1. **Matching through side conditions (the search).** An open `invs` condition is matched against each `invs`
   fact of the context. The match of two `Invs` builds the fact's combinator context (`Simplify.combinator`,
   called from the `Invs` case of `Rewrite.matches`), and `Simplify.iterations` simplifies the reads
   `earlier(natural(k), ⌊Z⌋)` of the dependencies there with all rules of the context. If the rule's left-hand
   side matches a rewritten read (`sum(js)` against the `sum(prefix(...))` that `earlier_sums` produces), the
   rule is tried again inside, its condition is searched against the same fact, one level deeper, until the
   step budget is exhausted. The cache `Context.combinators` does not help, since it is filled only after the
   inner context is complete. Instances: `sum_invs_const` (ps2-ll and 12 other translations at 0.34.22), the
   substitution lemmas of the first row_sums.dfy (finding 19), the exit lemma of the module `nested` with a bare
   comparison as left-hand side (finding 29).
2. **The decision of a condition (the instance).** `Rewrite.conditions` simplifies the instance of every
   conjunct with the full rules before it decides or matches it, and `Rewrite.holds` simplifies it again to
   decide. A condition that mentions the rule's own term, `l == current(Lv)` for a rule on `current(Lv)` with
   `Lv` bound, rewrites that term by the rule itself, whose conditions are evaluated again (findings 20, 32).
   This keeps the lower bound open and is the reason the summaries take `current(results(...))` as left-hand
   side instead of `results(...)`.

## The change

- `Context` gets a field `active: List[Rule]`, the rules whose conditions are being evaluated at this position,
  empty by default and copied along like the other fields, so that it reaches every nested context: `ctx.neutral`
  for the instances of conditions, the inner contexts of `Simplify.combinator`, the contexts of guards.
- `Rewrite.apply(rule)` skips a rule that is active (reference equality; the list has one or two elements) and
  evaluates the matching of the left-hand side and the conditions in `ctx.copy(active = rule :: ctx.active)`.
- `Context.key` includes `active`, so that inner contexts built while a rule is suspended are cached apart from
  the normal ones, whose reads that rule may rewrite.

About fifteen lines in `Context.scala` and `Rewrite.scala`.

## Why it addresses both

- Issue 1: the recursion needs the suspended rule to match the rewritten read inside the fact's context, which
  it is no longer offered. The reads are still rewritten by all other rules, so the match of the condition sees
  the same normal form as before, except for the one rule. A general left-hand side with an `invs` condition
  then costs one failed match per fact instead of the budget.
- Issue 2: the instance of the condition keeps the rule's own term as it is; `l == current(Lv)` is matched
  against the hypothesis `lo == current(L)` or decided from it, which is what the sound lower bound needs, and
  `results(...)` can be a left-hand side again.
- A guard on the same term instead of the same rule would not cover issue 1, where the term changes at every
  level (`sum(js)`, then `sum(prefix(natural(k), ...))`, ...).

## What it costs

A condition that needs the same rule on a different instance is no longer decided: a fragment lemma on a loop
nested three deep, or a lemma whose condition contains its own function on a subterm. No lemma of the database
is known to do this; the test suite and the SV-COMP databases will show if one exists. Under `-rules`, the
applications tried and rejected inside a former cycle no longer count.

## Verification

1. Build in the worktree, run the four test groups.
2. Issue 2: the sound lower bound (`pending/lower_bound/lb_cmp4.dfy`, the ties on the rule's own term) closes
   and its wrong program leaves a goal; the bubble sort summary with the left-hand side `results(...)` instead
   of `current(results(...))`.
3. Issue 1: the old exit lemma of the module `nested` on the cocktail program (`pending/nested_module/nested_a.dfy`),
   the first version of row_sums.dfy with its substitution lemmas (git history, before 1a20a02c), and the former
   `sum_invs_const` on `benchmarks/sv-comp/dafny/nla-digbench/ps2-ll.dfy` terminate instead of exhausting the
   budget; whether they close is a bonus.
4. The 30 algorithms against their expected outputs, then the sampled SV-COMP translations as in
   `pending/candidates/check.sh` (the examples of `examples/dafny/teq` and every fourth task of
   `benchmarks/sv-comp/dafny/expected.csv`), for proofs lost and time.
5. Two example tests in `examples/dafny/simplify`, one per issue, with expected outputs; doc/simplifier.md and
   doc/teq.md updated; the TODO entry and the item of teq-engine.md closed; version bump (minor).

## Not included

The other two remedies of the TODO entry: open conditions that contain combinators substituted but not
simplified before the search (remedy 2), and a separate budget for conditions whose exhaustion leaves the
condition undecided instead of aborting the command (remedy 3). Both are larger, and the guard makes them
unnecessary for the cycles seen so far; remedy 3 remains a safety net worth having.

## Result (Oct 12, 2026, version 0.42.3)

The guard as proposed cuts the re-entrance of one rule: the minimal lemma with a condition on its own term
(`examples/dafny/simplify/reentrant.dfy`) closes, and ps2-ll with the former `sum_invs_const` terminates in 4 s
with the goal it has without the lemma. The other cycles of `pending/` did not stop with the guard alone, and
their traces (`-debug rewrite`, a stack dump of the hanging run) showed two further mechanisms, each needing a
change of its own:

- **Chains of different rules.** Matching a condition against an `invs` fact builds the fact's combinator
  context, whose reads are normalized with all rules; a different rule with an `invs` condition is tried on a read,
  its condition builds another context, and so on through every such rule, each level trying every fact. The
  guard bounds the depth, not the branching. Fix: the reads of a context are normalized by the rules without an
  `invs` condition only (`Rule.plain`, `Simplify.iterations`).
- **Contexts rebuilt per position.** `Context.combinators` is keyed by the full outer context, which differs at
  every position where a rule is tried, so the context of a fact was rebuilt with the same reads rewritten a
  hundred times (the cocktail trace: 1000 steps, all on two reads). Keying by the suspended rules as first
  proposed made this worse. Fix: the reads are cached by the dependencies, the bound variables and the
  definitions of the traces (`Context.reads`), and the cache key of contexts does not include the suspended
  rules; a context built while a rule is suspended may lack that rule's rewrites of its reads.

With all three, the six cycle cases terminate (timeout 60 s, one core): the lower bound with closed ties (36 s),
the bubble summary with `results(...)` as left-hand side (9 s), the first row_sums with its substitution lemmas
(18 s), the cocktail program with the old nested module (18 s), ps2-ll with `sum_invs_const` (4 s), the minimal
lemma (closes). None of the five closes its goal: the summaries do not fire for the other reasons recorded
(the lower bound leaves its dependency variables unbound, finding 32), so the guard removes the non-termination,
not the obstacle. The 30 algorithms keep their expected outputs and run faster (cocktail sort 19 s instead of
34, row_sums 10 s instead of two minutes), since the work inside failed matches shrinks.
