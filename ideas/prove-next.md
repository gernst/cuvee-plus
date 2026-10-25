# Changes to the engine of `-prove`

The open changes to the engine, as of Oct 26, 2026 (0.51.1), ordered by the expected gain; what is done is
documented in [doc/prove.md](../doc/prove.md).

Done, by version: counterexamples by evaluation (`Prove.counterexample`, 0.46.13, 38 unsafe array-fpi tasks); case
splits on disjunctive premises (0.46.12: in-de20, in-de41, in-de42, in-de51), on guards that a loop does not change
and on remainders by small literals of goal variables (`Prove.alternatives`, 0.46.16, diamond_1-1); negative literals
as negated summands of the matcher (0.46.12); solutions `c == integer(n)` inlined like arithmetic ones
(`Linear.integer`, 0.50.16); rewrites modulo the classes (`Classes.within`) and roots by rank (`Classes.rank`), which
replaced the kludge of 0.50.17 for in-de62.2 (0.50.18); products matched modulo associativity and commutativity
(`Rewrite.matchesFactors`, 0.50.18, the family cohendiv).

## 1. Equalities from the simplex to the classes (Oct 26, 2026)

**Symptom.** `-slice` on `array-crafted/zero_sum1` (three loops: fill `a` with nondeterministic values, add them to
`sum`, subtract them again, `assert(sum == 0)`), after the fix of `maps_earlier` (bugs.md): the second loop leaves
`sum == sum(prefix(n₂, Tmp?))`, the third subtracts `sum(prefix(n₃, Tmp?))`, and the assertion holds iff
`n₂ == n₃`. The simplex knows `integer(n₂) == SIZE == integer(n₃)`, each from two inequalities (the exit test and the
bound of the iteration constraint), but no equation `n₂ == n₃` reaches the classes, so the two sums stay different
terms and `Slice` does not decide the assertion (`-svcomp` still proves the task, by its case splits).

**Diagnosis.** The classes and the simplex do not share their equalities: `Forward` assumes an instance that the
rules reduce to true as it is, "since it may still be news to the arithmetic, whose constraints do not see the
equations of the classes" (Forward.scala), and `zero_integer_value` (teq.dfy) exists only to carry `n == zero` of the
classes into the simplex. Item 2 (the normal form of the arithmetic atoms) covers classes → simplex; nothing covers
equalities that the simplex implies between atoms, which congruence would need for `prefix(n₂, xs)` and
`prefix(n₃, xs)`.

**Not a fix: injectivity of `integer`.** The database has the rewrite rule already, `integer_injective`
(`(integer(m) == integer(n)) <==> (m == n)`) and `integer_eq`, for equations that occur. A case of `Simplify.eq_` that
decides `n == m` on naturals by the simplex (`implied`/`denied` of `integer(n) == integer(m)`) was tried and removed:
sound and free of cycles (a decision, no rewrite, unlike the cycle through `integer` that the comment of
`Classes.within` describes), but nothing asks `n₂ == n₃`, the assertion is a polynomial over the two sums.

**Change.** After a fact is assumed, check the atoms `integer(n)` against each other, the pairs whose difference the
constraints bound to 0 from both sides, and merge their naturals in the classes; cost unknown, measure on the task
sets (the number of atoms `integer(n)` of a goal is small, one per loop).

## 2. Normal form of the arithmetic atoms (stage 3)

0.50.18 rejects rewrites whose result contains their own term modulo the classes and chooses the roots of classes by
rank (done, above). Open, a third stage: the normal form of the arithmetic atoms in the simplifier, a registered atom
of sort Int or Real replaced by the root of its class, with `Linear` built from the normalized facts and rebuilt after
merges; then `c * c` and `integer(n) * integer(n)` coincide in general, and `Linear.integer` is a special case. Only for
arithmetic atoms: traces, lists, histories and binders stay as they are, since views, the selection of dependencies,
`self` and `Canon` depend on their syntax. Matching keeps going through the members of a class (normalizing alone
would miss matches through a definition that is not the root). About 100 lines and many changed expected outputs; to
be prepared on a branch with a comparison on all task sets, once a further monomial gap or loop calls for it, and
together with item 1, the other direction.

## 3. Naturals and integers

**Measured.** The conversions dominate the rule statistics (`scripts/rules.py`, the proved tasks, upper bounds).
Runs of Oct 24-25, 2026 (0.50.18 without the fallback, 0.51.0 with it, 120 s): 40882 of 66134 applications (61.8 %)
without the fallback, 52105 of 83227 (62.6 %) with it, 70 % in Arrays, 55 % in Loops; the four most frequent rules are
conversions, `natural_positive` (20060 applications in 227 tasks with the fallback; a forward lemma,
`0 < x ==> natural(x) != zero`), `integer_natural` (15690, 345 tasks), `integer_zero` (8131, 60 tasks) and
`zero_integer_value` (6835, 70 tasks; a forward lemma that carries `n == zero` into the simplex), ahead of the first
rule about traces, `earlier_counter` (3808). The two rules about `zero` grew with the module series (157 and 113
applications in the runs before Oct 14, 2026, where the share was 60 % as well).

**Option: counts as integers.** The distinction pays for the definitions and the Lean proofs (structural recursion on
`zero`/`succ` in `counter`, `consts`, `earlier`, `prefix`; non-negativity by the type; rules on the base and step
cases), and costs in the engine: two names for one quantity (`n` in the classes, `integer(n)` in the simplex), the
conversion rules and `0 <= integer(n)` at every loop, `Linear.integer`, the cycles of in-de62.2 and of
`Classes.within`, the special cases of natural constants (`natural(4294967296) == zero`) and of the counterexample
search; `-fallback` lowers naturals to integers anyway. The alternative: counts and lengths of sort `int`, the
definitions clamped (`counter(i, c, n)` stops for `n <= 0`, as `natural` clamps now), the Lean proofs by `toNat` (as
`natural` is defined), the cases `zero`/`succ` of the rules as conditions `n <= 0`/`0 < n` that the simplex decides.
It removes the conversions, not the gap of item 1: `prefix(n₂, xs)` and `prefix(n₃, xs)` still need `n₂ == n₃` in the
classes, although integer counts are polynomials, into which `Linear.solved` inlines the solutions of equations
already. A migration of the database, its proofs, TEQ and the rules: decide after the measurement of the conversions
on current runs, and only together with item 1.

## 4. Integer reasoning about remainders

**Symptom.** The strided stores (array-tiling `mbpr*`, `pr*`, `pnr*`, 22 true tasks): the rules of `teq:strides` fire
on mbpr2, open is `(i - 1) % 2 == 0` against `i % 2 == 0` for a variable bound by a combinator. The simplex is
rational; a forward lemma `x % 2 == 0 || (x - 1) % 2 == 0` does not close it; the case splits of
`Prove.alternatives` cover remainders of goal variables only (on pr3, the split of the guards fixes the case of the
store, three levels deep, but the leaves stay open on the remainders of the strides, 18 s to 42 s to `unknown`).

**Change.** Remainders by a literal `m` as a fresh integer variable `r` with `0 <= r < m` and `x == m q + r`, also
for bound variables, with the cases of `r` for small `m`; or a normalization of `(x + c) % m` to `(x % m + c) % m` with
the cases of `x % m`. Check on mbpr2 first.

## 5. Depth of the case splits

in-de52 and in-de62 have more loops than the four levels of the splits of `Prove.cases`; sum_by_3_abstracted stays
open at any depth. Instead of a larger depth: split on the disjunctive premise whose `_cases` rule enables the most
rules, or iterate the depth (2, 4, 8) within the time limit. Considered and not done (Oct 14, 2026): loop
unswitching before `-teq` (it doubles the copies with each condition and the code after the loop); a disjunctive
conclusion moved into the premises (no gain).

## 6. Rounds that do not settle (26 tasks)

**Symptom.** array-crafted bAnd*, bor*, xor*, reducercommutativity avg*, sum*, data_structures_set_multi_proc_ground-2
end in "rewriting does not terminate" (the 1000 steps of a goal used up) since `natural_positive` (teq.dfy) and
`store_occurs_selects` (search) are forward lemmas; they were `unknown` before, so nothing correct is lost, but each
run takes up to the time limit (bugs.md, performance).

**Diagnosis** (sum05-2 with `-debug rewrite,forward`): the same instances are assumed again in every round
(`natural_positive at natural(5)` 173 times, `store_occurs_selects` 1008 times), and the same terms are rewritten
again (`integer(n)` to `5` 508 times, where `n == natural(5)`), by the simplification of the instances in
`Forward.fire`, repeated wherever a lemma fires without a memo; bAnd*, bor*, xor* use up the steps in the traversal
itself (the same reads x[0], x[1] in about 31 sibling contexts). Both rules are conversions of item 3.

**Tried and reverted.** Steps of their own for an instance (0.46.8, 0.46.9): errors fall from 58 to 38 on Arrays at
60 s, timeouts rise from 76 to 95, the same correct results. A memo of the simplified instances (0.50.15, Oct 24,
2026): few hits, since the traversal builds the context of each position from its parent; the user's decision: a cache
is not worthwhile, it was tried before. The open regression of ps2-ll_unwindbound1 (31 s with 0.46.8, a timeout at
60 s since 0.46.13) belongs here (bugs.md).

## 7. Evaluation of closed instances of the database

Deprioritized (the user's decision, Oct 2026: counterexamples are not of interest). 30 unsafe array-fpi tasks remain
unknown, e.g. brs2f leaves `sum(map(⌊counter(0, 1, n)⌋, k :: if 0 < k then (if k % 2 == 0 then 20 else 0) else 0))
<= 2 N`, false at N = 3, since `Prove.counterexample` evaluates only the functions of `Eval.computed`. The change would
compute the variables that a premise determines and evaluate ground instances of the database by their definitions
(`counter`, `current`, `butlast`, `earlier`, `prefix`, `sum`, `count`, `max`; `maps` and `trace` directly), inside
the search for a counterexample only, which can only turn a goal into `false`; up to 30 false.

## Not in the engine

indp5, revcpyswp2, sum_array-2-2 (timeouts at 60 s, lost against 0.42.1), the recurrences of `ifcomp` (a general sum
of squares with exact division), `pcomp`, `sqm-if`, `condm`, the conditional stores of partial_mod_count_*, and the 15
algorithms not verified under `-teq -prove` (TODO.md) are work on the database and the examples first (the work queue
of TODO.md).
