# State traces with projections: the sketch

> Superseded as a plan by [deduction-engine-plan.md](deduction-engine-plan.md) (Oct 13, 2026); kept for the
> findings and the conclusion. The implementation is the package `prove` on the branch `prove`, see
> [deduction-engine-implementation.md](deduction-engine-implementation.md).

Plan of Oct 12, 2026 for section 4 of [deduction-engine.md](deduction-engine.md) (the conclusion of
[doc/array-algorithms](../doc/array-algorithms), "an interface, not the sole carrier"): a loop is one fold over
its state, the per-variable trace equations are projections of it. The sketch lives in the worktree
`.claude/worktrees/state-trace` (branch `worktree-state-trace`), where Scala changes are allowed; nothing in the
main checkout changes but this file.

## The idea

A loop over variables x̄ is semantically one fold over the iterations, `S == trace(s̄₀, for ⌊K⌋ do s̄, k :: F(s̄, k))`
with the state as the accumulator. Today's trace equation system is this fold decomposed by projection: one
trace per variable, the histories ⌊Y⌋ of the others as dependencies. The decomposition is what lets a small
lemma meet each equation when the dependencies layer (counter, index, array, sum); it is the obstacle when
they do not: mutually dependent pointers (merge, binary search, gnome sort) give equations that only make
sense together, inner loops become fresh sequences scattered into fragments over incomparable dependency
lists. The sketch keeps the per-variable equations as the interface to the database, makes the state trace the
carrier, and derives the per-variable form by one projection rule, reusing the matcher's synthesis of
variable dependencies as maps.

**State of the plan (end of Oct 12, 2026).** Steps 1 and 3 are done as written; step 2 was superseded by the
experiment: the projection is not a rewrite of the simplifier but a marker left in place, which the matcher matches
modulo its simplified view, with a guard on the act of projecting and a replacement by the view only once it is
closed (see the findings and the conclusion below). Step 1 additionally substitutes the closed definitions of a
loop, so that an inner loop is a value of the outer update.

## Step 1: the state trace (`-teq-state`)

A flag `-teq-state` beside `-teq`, so both forms are compared on the same files. It injects a fresh database:
`core.dfy` only (the types, the functions on traces, the shared definitions), and a new module
`resources/cuvee/teq/state.dfy` for the lemmas that the examples need, written for the state form.

For a loop with modified variables x̄ = x₁, ..., xₘ (m ≥ 2), `TEQ.loop` emits a datatype per loop whose
selectors are named like the variables, returned as a declaration in the command list ahead of the goal
(later stages pick it up in the state):

```
datatype State_p = State_p(x₁: T₁, ..., xₘ: Tₘ)        -- fresh name per loop
K == counter(0, 1, n)
S == trace(State_p(x̄₀), for ⌊K⌋, Z? do s, k, z :: case B₁ => State_p(F̄₁(s, z)) case B₂ => ...)
xᵢ == xᵢ(current(S))                                   -- the exit state, the selector applied
invs(for ⌊K⌋, ⌊S⌋, Z? check k, s, z :: guard(s) && paths(s, z))
0 <= integer(n)
```

The body reads xⱼ as the selector `xⱼ(s)`. Loops with one modified variable keep today's form. The safety
check and the exits stay as they are, over the exit state.

**The dependency question.** Whether the single equation needs ⌊S⌋ among its own dependencies, the way
today's trace of x lists ⌊Y⌋ of the others. Expectation: the update reads only the accumulator, so the trace
itself needs none; the iteration constraint needs ⌊S⌋, since `invs` has no accumulator. Consequence for inner
loops: in the state form the inner counter and the inner state trace are closed terms over the outer
accumulator and the inner number of iterations (no mutual recursion between traces), so only that number and
the inner choices stay as list-valued dependencies, where today I over ⌊J⌋ and J over ⌊I⌋ cannot be
substituted. Both variants are built and tested.

## Step 2: projection in the simplifier

A built-in helper next to `Simplify.trace`, not lemmas, since the arity and the substitution inside the update
vary. For `S` defined as above (found through the context, `ctx.↑`, like counters today), the projection of
component i is

```
πᵢ(S) = trace(xᵢ₀, for ⌊K⌋, ⌊S⌋, Z? do x, k, s, z :: Uᵢ[xᵢ(s) := x])
```

with Uᵢ the i-th component of each case (the selector applied to the constructor reduces). Three rewrites use
it: `xᵢ(current(S))` to `current(πᵢ(S))`, `xᵢ(earlier(j, ⌊S⌋))` to `earlier(j, ⌊πᵢ(S)⌋)`, and the synthesized
`maps(for ⌊S⌋ yield s :: xᵢ(s))` to `⌊πᵢ(S)⌋`. The crux is the chain inside a combinator over ⌊K⌋, ⌊S⌋: the
iteration facts give `s == earlier(natural(k), ⌊S⌋)`, so a read of the counter component becomes
`earlier(natural(k), ⌊πᵢ(S)⌋)`, then k, and the lemmas on sums and stores meet the shapes they were written
for. `Simplify.deps` drops ⌊S⌋ once unused, which is how the counter lemma fires on a projection.

## Step 3: experiments

From a private jar in the worktree, with timeouts, recorded in `NOTES.md` of the examples folder. The goal is 5
to 10 working examples that verify in under 20 s each, starting with a loop that swaps two arrays
component-wise, then layered single loops (sum, copy, init, counter), then mutually dependent pointers (merge,
binary search) and nested loops (nested_sum, the two minimal problems), as far as the budget goes. For each:
which lemmas match the projected forms, which need the maps or earlier forms, which lemmas the fresh database
needs, and the answer to the dependency question from the variants.

## Out of scope

The fallback lowering of the state datatype, the Lean semantics, the C frontend, changes to the main checkout.
No commit; the findings are reported.

## Findings (Oct 12, 2026, first session)

State of the worktree: the flag, the fresh module (32 lemmas copied from the modules of `-teq`), the state form of
`TEQ.loop`, the projection in the simplifier and the matcher; examples/dafny/state/swap.dfy. Verified with
`-teq-state -simplify` on the fresh module: the swap of two arrays (2.3 s; a wrong postcondition leaves
`b[k] == a[k]`), counter, copy, init (about 1 s each). Residues: sum.dfy and lsearch.dfy (the sums and search
lemmas were added to the module afterwards, not yet run), argmax and reverse (not analyzed); bsearch (lo and hi
read each other) does not finish in 20 s; prefix_sums and merge need `sum` and `count`, which the module lacks.

1. **The projection is a marker, matched modulo its view.** A read of a component of the state trace,
   `State_x(current(S))`, `State_x(earlier(j, ⌊S⌋))` (also through a bound variable `s` of a combinator over
   ⌊S⌋, which denotes `earlier(natural(k), ⌊S⌋)` by `Simplify.iterations`), or `maps(for ..., ⌊S⌋ yield ..., s ::
   State_x(s))`, stays in the term. When a pattern does not match it as it is, the matcher matches it against the
   simplified view `current(π_x(S))`, `earlier(j, ⌊π_x(S)⌋)`, `⌊π_x(S)⌋`, with `π_x(S)` the per-variable trace
   over ⌊K⌋, ⌊S⌋ whose accumulator is the own component (`Simplify.view`, `Simplify.projected`,
   `Rewrite.matches`). This is the mechanism by which the matcher follows the definition of a variable through the
   context (`Context.↑`), applied to a term instead of a variable: the state trace is one equation, the
   per-variable equations are not stated, and the lemmas of the database meet them anyway.
2. **Eager projection regresses.** Rewriting `State_a(s)` to `earlier(k, ⌊π_a(S)⌋)` in place unfolds the projection
   of `b` inside that of `a` and vice versa without end, since each projection reads the other component. A
   guard by the position in the term (the update of a projection) does not help: the fold of the projection into
   `stores(a, keys, values)` moves the reads into the `maps` arguments, which are simplified again in the outer
   context. The guard must be dynamic: while the view of component `x` of `S` is being simplified for a match,
   `x` is not projected again (`Context.projecting`); an inner read of `x` stays a marker, which the rules treat
   as an opaque value, e.g. one stored into the other array, and which the lemma on earlier stores drops with its
   branch. Views are memoized per command by the marker and the context (`Context.projections`), as the contexts
   of combinators are; a view computed while another component was suspended may be weaker than one computed
   outside, which the memo does not distinguish (not observed to matter yet).
3. **Layered components are evaluated.** A component whose projection reads no other component, e.g. the counter
   `i`, is replaced by its simplified view in place (`State_i(s)` becomes `k`, `Simplify.app`), which cannot
   regress. Without it the decision procedures do not see that the marker is `k`:
   `occurs(State_i(s), ⌊counter(0, 1, natural(k))⌋)` stays undecided and the mutual dependency of the arrays is
   not cut. The per-variable form has the same step as the replacement of the bound variable `i` by `k`
   (`Simplify.iterations`, chains). Whether the condition "reads no other component" is the right one, or whether
   it should be "the view contains no marker", is open; the first is syntactic and cheap.
4. **The dependency question.** The state trace needs only ⌊K⌋ and the choices as dependencies: the accumulator
   carries the state. The iteration constraint needs ⌊S⌋, since `invs` has no accumulator. A projection needs
   ⌊S⌋ exactly when its component reads another one; `Simplify.deps` drops it otherwise, so the projection of a
   counter is the plain counter and `counter_def` applies unchanged. In the state form the inner counter and
   state trace of a nested loop are closed terms over the outer accumulator and the inner number of iterations
   (not tried yet).
5. **The fresh module.** Every lemma that the per-variable form uses applies to the views unchanged; the module
   needs the arithmetic on naturals (`integer_natural`), without which the counter's view is
   `integer(natural(k))` and nothing matches, and `maps_identity` (`maps(for xs yield x :: x) == xs`), since the
   keys of the stores are a map of the evaluated counter rather than ⌊I⌋ itself.
6. **Costs.** The view of a component is simplified in the context of each position where a rule tries it,
   memoized by context; the swap takes 2.3 s against 1 s for the per-variable form. The views of the counter are
   recomputed in each new combinator context (the bound variables are renamed), which the memo does not share.

## Findings on nested loops (Oct 12, 2026, second session)

With the closed definitions substituted (`TEQ.loop` under `-teq-state`: the counter, the state trace, and the exit
values of a loop are terms over its number of iterations and its choices, since no trace depends on another), an
inner loop is one value of the outer update, `current(trace(State_j(s), for ⌊counter(0, 1, n₇)⌋ do j, k :: j + 1))`,
and the only fresh sequence of the outer loop is the list `N?` of the inner numbers of iterations. The nested sum
then simplifies, without the module `nested` or any lemma on fragments, to

```
invs(for ⌊counter(0, 1, n₁₃)⌋, N? check k, n₇ :: n == integer(n₇))
  ==> sum(maps(for ⌊counter(0, 1, n₁₃)⌋, N? yield k, n₇ :: integer(n₇))) == m * n
```

where the fragments problem of the per-variable form (six constraints over incomparable dependency lists, each
resolved by its own lemma) does not arise: the inner test and exit are decided inside the outer iteration, where
they bind the same `s` and `n₇`. Two lemmas close this and the other nested examples: `integer_eq`
(`integer(n) == x <==> n == natural(x)` for `0 <= x`, the number of iterations determined by its value) and
`consts_choice` (`invs(for ⌊counter(0, 1, n)⌋, xs check k, x :: x == c) <==> xs == ⌊consts(n, c)⌋`, a choice whose
values the constraint determines is a constant list, whose reads `earlier(j, xs)` then resolve). Neither is in the
database of `-teq`; both are arithmetic and lists, not loop shapes.

| example | per-variable form | state form, fresh module |
|---|---|---|
| nested_sum | `teq:nested` (4 fragment lemmas), `consts_prefix_def`, `sum_consts_prefix`, `mul_eq_cancel` | 2.0 s, no example lemma |
| nested_mult | `teq:nested`, `mul_eq_cancel` | 3.1 s, no example lemma |
| nested_counter | database | 1.9 s, no example lemma |
| row_sums | `teq:nested`, 2 chain lemmas | 3.8 s, no example lemma |
| transpose | `teq:nested`, 2 folds (`results`, `column`), 4 lemmas | 7.0 s, 1 summary lemma on the nested fold |

The summary lemma of the transpose states the program's shape literally, `current(trace(B0, for
⌊counter(0, 1, natural(m))⌋ do B, k :: current(trace(B, for ⌊counter(0, 1, natural(n))⌋ do Bi, ki :: Bi[ki :=
Bi[ki][k := A[k][ki]]]))))[j][i] == A[i][j]`; the inner number of iterations is written `natural(n)`, since the goal
binds it to a choice `n₈` with `n₈ == natural(n)` from `consts_choice`, which the matcher follows through the
definition, while a rule variable in that position would capture the bound `n₈` and is refused.

Ten examples verify with `-teq-state -simplify` and the module alone (examples/dafny/state, each with its expected
output): counter, copy, init, lsearch, swap, nested_counter, nested_sum, nested_mult, row_sums, transpose; the
longest is the transpose at 7 s. sum.dfy leaves `2 * ((-n + n * n) / 2) + n == n * n`, as the per-variable form
does. Open: bsearch, whose `lo` and `hi` read each other under guards, does not finish in 20 s: not a cycle (21
rewrite steps in 8 s) but the views of the two components, each a guarded trace simplified while the other is
suspended, recomputed in nine contexts each; the fresh module also lacks the `incs`/`decs` lemmas of `search.dfy`
that the per-variable proof uses with a cut. A memo of views across contexts, or views computed once per round,
is the next step for the mutual case.

The matcher's fallback (a marker matched modulo its view whenever a direct match fails) is tried for every
selector application of any datatype; `Simplify.view` returns none unless the argument is the current or an
earlier value of a state trace, so the cost outside `-teq-state` is a lookup per selector application.

## Conclusion: does the approach help?

Yes, and the experiment sharpened what the idea is.

**The content is not "one trace instead of many": the per-variable equations stop being facts and become views.**
In the per-variable form, symbolic execution commits to a decomposition up front: every variable gets an equation,
every other variable's history becomes a dependency, and the matcher has to reassemble the product afterwards
through open trace variables, pins, and the bookkeeping of dependency lists. In the state form the decomposition is
never stated. The fold over the state is the only fact, and a projection exists exactly at the moment a rule asks
for it, in the context where it asks. That is the move the engine already makes for variables: a definition in the
context is followed when a pattern needs it, never rewritten in place (`Context.↑`). The marker generalizes this
from variables to terms, which is why the lemmas keep their form. The answer to the paper's question is therefore:
trace equation systems are the right interface, and the right carrier is not a system of equations at all but one
fold plus a lazy projection.

**The dependency question has a clean answer.** The state trace needs no trace as a dependency: the accumulator
carries the state, the constraint ranges over its history, and a projection ranges over the state history exactly
when its component reads another one. Because no trace depends on another, every trace, counter, and exit value is
a closed term over the number of iterations and the choices. That is what makes an inner loop a value of the outer
update rather than a family of fresh sequences, and it is a property only the state form has: in the per-variable
form the equations are mutually recursive and cannot be substituted. The fragments problem was never about
fragments; it was the quantification over sequences that the decomposition forced.

**What the experiment taught about laziness.** The views cannot be eager, and not merely for cost: two components
that read each other have projections that unfold each other, and no positional guard survives folding, since
folding moves the reads into arguments that are simplified again elsewhere. The guard has to be on the act of
projecting, not on the term (`Context.projecting`). In the per-variable form this problem was hidden, because the
mutual recursion lived in variable definitions that were followed only on demand. The state form made the same
fact explicit and forced the mechanism to be stated.

**Two residual tensions, both about the engine, not the carrier.** First, a marker must sometimes be evaluated
after all: the arithmetic cannot decide anything about `State_i(s)`, so a component whose view is closed is
substituted, which is the old replacement of `i` by `k` in a new guise; the criterion "the view reads no
component" works but is a heuristic about the decision procedures, not about the representation. Second,
determined choices: the number of inner iterations is fixed by the exit, but it is still a choice list, and the
lemma that turns a determined choice into a constant list (`consts_choice`) is a one-point rule over sequences
that an engine should own. This is consistent with the diagnosis of [deduction-engine.md](deduction-engine.md).

**What it does not change.** The mutual case under guards, the binary search, still needs the views of both
components simplified against each other, and the method still needs a lemma that knows what a loop computes (the
transpose). The state form removes the reconstruction, not the knowledge.

**Recommendation.** Take the representation into the engine plan as its phase 4, ahead of the triggers, with the
memo of views across rounds as the first engineering task and the binary search as its test.
