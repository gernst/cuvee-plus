# Changes to the engine of `-prove`

The open changes to the engine after the migration of the lemma database (doc/teq.md), as of Oct 14, 2026 (0.46.14;
SV-COMP at 60 s with 0.46.13: Arrays 144 true, 53 false, Loops 148 true, 24 false, no wrong answers). Ordered by the
expected gain; what is done is documented in [doc/prove.md](../doc/prove.md): case splits on disjunctive premises
(`Prove.cases`, 0.46.12: in-de20, in-de41, in-de42, in-de51), counterexamples by evaluation (`Prove.counterexample`,
0.46.13: 38 unsafe array-fpi tasks), negative literals as negated summands of the matcher (0.46.12).

## 1. Evaluation of closed instances of the database

**Symptom.** 30 unsafe array-fpi tasks remain unknown; brs2f leaves `sum(map(⌊counter(0, 1, n)⌋, k :: if 0 < k then
(if k % 2 == 0 then 20 else 0) else 0)) <= 2 N`, false at N = 3. `Prove.counterexample` skips goals with traces and
uninterpreted functions.

**Change.** Extend the evaluator of `Prove.counterexample` to the combinators of teq.dfy (`counter`, `map`, `sum`,
`count`, stores and selects) for literal bounds: once N is assigned, `n` follows from the premises, and the trace is
a finite list. An evaluator, not rules: unfolding traces is excluded from the database. Expected gain: up to 30 false.

## 2. Integer reasoning about remainders

**Symptom.** The strided stores (array-tiling `mbpr*`, `pr*`, `pnr*`, 22 true tasks): the rules of `teq:strides` fire
on mbpr2, open is `(i - 1) % 2 == 0` against `i % 2 == 0`. The simplex is rational; a forward lemma `x % 2 == 0 ||
(x - 1) % 2 == 0` does not close it.

**Change.** Remainders by a literal `m` as a fresh integer variable `r` with `0 <= r < m` and `x == m q + r`, and
the case split of `Prove.cases` over the `m` values of `r` for small `m`; or a normalization of `(x + c) % m` to
`(x % m + c) % m` with the cases of `x % m`. Check on mbpr2 first.

## 3. Rounds that do not settle (26 tasks)

**Symptom.** array-crafted bAnd*, bor*, xor*, reducercommutativity avg*, sum*, data_structures_set_multi_proc_ground-2
end in "rewriting does not terminate" (the 1000 steps of a goal used up) since `natural_positive` (teq.dfy) and
`store_occurs_selects` (search) are forward lemmas; they were `unknown` before, so nothing correct is lost, but each
run takes up to the time limit (bugs.md, performance).

**Diagnosis** (sum05-2 with `-debug rewrite,forward`): the same instances are assumed again in every round,
`natural_positive at natural(5)` 173 times, `store_occurs_selects` 1008 times in total, and the same terms are
rewritten again, `integer(n)` to `5` 508 times, where `n == natural(5)`. The 1000 steps of the goal are used up
inside one traversal, by the simplification of the instances in `Forward.fire`, which is repeated wherever a lemma
fires (at every assumed fact and at every comparison decided by `Simplify.forward`) without a memo; the firing at
every assumed fact is quadratic in the conjuncts of a premise. bAnd*, bor*, xor* use up the steps in the traversal
itself: the same reads x[0], x[1] are simplified again in about 31 sibling contexts.

**Tried and reverted (0.46.8, 0.46.9).** Steps of their own for an instance: the reducercommutativity tasks end
`unknown` instead of breaking off, but on Arrays at 60 s the errors fall from 58 to 38 and the timeouts rise from 76
to 95, with the same correct results.

**Change, if the cost matters.** A memo of the instances per context: an instance whose canonical form (`Canon`,
modulo the classes) is known is not assumed again and does not count as a change of the round. Narrower: a raw
instance is assumed only if one of its atoms is not yet in the classes. The repeated firing of `Forward.saturate`
can go once examples/dafny/state/bsearch_sorted.dfy no longer needs it. Check: the 26 tasks end `unknown` in seconds,
bsearch_sorted and the examples unchanged, a cloud run against 0.46.13. Also the regression of ps2-ll_unwindbound1
(31 s with 0.46.8, a timeout at 60 s with 0.46.13; bugs.md).

## 4. Deeper or better-chosen case splits

in-de52 and in-de62 have more loops than the four premises of `Prove.cases`; sum_by_3_abstracted stays open at any
depth. Instead of a larger depth: split on the disjunctive premise whose `_cases` rule enables the most rules, or
iterate the depth (2, 4, 8) within the time limit.

## 5. Products modulo commutativity

The matcher matches sums modulo associativity and commutativity, products not: `div_quotient_remainder` (legacy) does
not match `k * m` (TODO.md); `ifcomp` needs products matched modulo commutativity with a general sum of squares.
Low priority until such a lemma is in the database.

## Not in the engine

indp5, revcpyswp2, sum_array-2-2 (timeouts at 60 s, lost against 0.42.1), the recurrences of `ifcomp`, `pcomp`,
`sqm-if`, `condm`, the conditional stores of partial_mod_count_*, and the 15 algorithms not verified under `-teq
-prove` (TODO.md) are work on the database and the examples first (ideas/work-queue.md).
