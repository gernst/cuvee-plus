# Changes to the engine of `-prove` after the database migration

Oct 13, 2026, after the migration of the lemma database (ideas/teq-modules.md) and the runs on SV-COMP at 60 s
(0.46.5: Arrays 145, Loops 161 correct, no wrong answers). A plan, not implemented; ordered by the expected gain.

## 1. Rounds that do not settle (26 tasks)

**Symptom.** array-crafted bAnd*, bor*, xor*, reducercommutativity avg*, sum*, data_structures_set_multi_proc_ground-2
end in "rewriting does not terminate" (the 1000 steps of a goal used up) since `natural_positive` (teq.dfy) and
`store_occurs_selects` (search) are forward lemmas; they were `unknown` before, so nothing correct is lost, but each
run takes up to the time limit.

**Diagnosis** (sum05-2 with `-debug rewrite,forward`): the same instances are assumed again in every round,
`natural_positive at natural(5)` 173 times, `store_occurs_selects` 1008 times in total, and the same terms are
rewritten again, `integer(n)` to `5` 508 times, where `n == natural(5)`. The outer rounds of `Simplify.apply` do
not repeat (no round completes); the 1000 steps of the goal are used up inside one traversal, by the
simplification of the instances in `Forward.fire`, which is repeated wherever a lemma fires: at every assumed fact
and at every comparison decided by `Simplify.forward`, without a memo.

**Done (0.46.8).** The steps went into the simplification of the instances, which `fire` repeats wherever a lemma
fires (also at every comparison decided by `Simplify.forward`): an instance is simplified with steps of its own now.
The reducercommutativity tasks end `unknown` (sum05-2 in 32 s); bAnd*, bor*, xor* still use up the steps of the goal,
in the traversal itself: the same reads x[0], x[1] are simplified again in about 31 sibling contexts. Both outcomes
score the same; what remains is the cost.

**Further change, if the cost matters.**
- A memo of the instances per context: an instance whose canonical form (`Canon`, modulo the classes) is known is
  not assumed again, and does not count as a change of the round (step 3 of J in ideas/teq-modules.md, "firing at
  definitions, a memo per lemma and canonical term").
- Alternatively, the narrower fix: a raw instance is assumed only if one of its atoms is not yet in the classes.
- Check: the 26 tasks end `unknown` in seconds, bsearch_sorted and the examples unchanged (the repeated firing of
  `saturate` is still needed there), the full suite, a cloud run against 0.46.5.

## 2. Splitting disjunctive premises in `-prove`

**Now.** The `_cases` rules of `mods` (teq:unsigned) introduce premises `n == zero || integer(n) < 1`, which `-prove`
does not split; the benchmark definitions run a second round of `-split -prove` (7 tasks of Loops, among them
in-de20, in-de31, in-de32, sum_by_3), which costs a full pass over all remaining goals.

**Change.** None necessary. If the cost of the second round shows in the timeouts, `Prove` could split a premise
that a rule turned into a disjunction of two atoms, at most once per goal, and prove both cases.

## 3. Refutation by substitution (1 task)

`while_infinite_loop_4` (expected false) leaves `not (n == zero && 0 <= integer(n))`, which is false for `n = zero`.
`-prove` does not substitute a variable that a premise equates with a constructor before deciding a goal false.
**Change:** in the refutation of a goal (`-verify`), substitute variables by the literals and constructors of their
classes and simplify; small, but one task only.

## 4. The cost of forward lemmas

With 3 more forward lemmas the median time on the solved tasks did not change (22.5 s, 11.9 s), but the firing at
every assumed fact is quadratic in the conjuncts of a premise (ideas/teq-modules.md). The memo of 1 is the first
step; the repeated firing of `saturate` can go once examples/dafny/state/bsearch_sorted.dfy is retired.

## 5. Products modulo commutativity

`div_quotient_remainder` (legacy) does not match the product `k * m` of the normal form (TODO.md). Low priority:
no task of SV-COMP is known to need it.

## Not in the engine

The remaining lost tasks against 0.42.1 (indp5, revcpyswp2, in-de41 to in-de62, sum_by_3_abstracted, sum_array-2-2)
and the retirement of `teq:nested` (the nested sorts loop with `teq:sorted`) are work on the database and the
examples first; whether the sorts need the engine is open.
