# The state-trace sketch, reviewed against the engine plan

Oct 12, 2026. A reading of [state-trace.md](state-trace.md) and of the commit b6f2b969 on the branch
`worktree-state-trace` (`-teq-state`, version 0.43.0 on the branch, not merged) from the perspective of
[deduction-engine-plan.md](deduction-engine-plan.md), whose section 1 was written before the sketch's second
session: what is new, where the sketch differs from what the plan expected, and why.

## New key insights

- **Nested loops work without any fragment lemma.** Since in the state form no trace depends on another, the
  counter, the state trace and the exit values of a loop are closed terms over its number of iterations and its
  choices, and they are substituted. An inner loop is then one value of the outer update, and the only fresh
  sequence of the outer loop is the list of the inner numbers of iterations. Five nested examples verify
  (nested_sum 2 s, nested_mult 3 s, nested_counter 2 s, row_sums 4 s, transpose 7 s) with two generic lemmas that
  are not loop shapes at all: `integer_eq` (`integer(n) == x <==> n == natural(x)` for `0 <= x`) and
  `consts_choice` (a choice whose values a constraint determines is a constant list), a one-point rule over
  sequences that, as the note says, an engine should own.
- **The reframing.** The fragments problem "was never about fragments; it was the quantification over sequences
  that the decomposition forced." And: the per-variable equations stop being facts and become views; the carrier
  is one fold plus a lazy projection, which generalizes `Context.↑` from variables to terms.
- **The state form removes the reconstruction, not the knowledge.** The transpose still needs one summary lemma
  on the nested fold, written literally; the binary search is still open, not from a cycle (21 rewrite steps in
  8 s) but because the views of `lo` and `hi` are recomputed in nine contexts each.

## Where the sketch differs from the plan, and why

1. **No derived equations in the context.** The plan (step S3) recorded the per-variable equations as equations of
   the context once a projection is rewritten to a closed form. The sketch never states them: a projection exists
   only at the moment a rule asks for it, in the context where it asks. This is the right call, because stated
   per-variable equations of a joint fold are mutually recursive again, which is exactly what the state form
   avoids.
2. **No ghost components.** The plan (step S4) made the inner loop's number of iterations, counter and trace
   components of the outer state. The sketch needs none of this, because the closed substitution makes the inner
   trace a term over the outer accumulator. The plan missed it by reasoning from the per-variable form, where the
   equations are mutually recursive and fresh variables are unavoidable; with a single accumulator that
   constraint is gone.
3. **Views, not rewrites.** The plan (step S2) rewrote the reads of components to projections in place. Finding 2
   of the sketch shows that this regresses as soon as two components read each other, since each projection
   unfolds the other, and that no positional guard survives folding, since folding moves the reads into arguments
   that are simplified again elsewhere. The sketch matches the markers modulo their view when a direct match
   fails, with a dynamic guard `Context.projecting` on the act of projecting. That is the re-entrance guard of
   [reentrance-guard.md](reentrance-guard.md) in a second guise, found the same day: suspension while computing
   something about itself. The two should become one facility in `Context`.
4. **A datatype per loop, not the tuples of the prelude.** The selectors are named like the variables, so a
   marker identifies the loop and the variable, which is what the suspension set keys on (`projecting: Set[Fun]`),
   and the datatypes are declared ahead of the goal. Better than the plan's tuples.
5. **The memo key is too fine.** The views are memoized by `(marker, ctx.key)`, the full outer context, the same
   key that made the first version of the guard's cache rebuild the context of a fact at every position. That is
   where the binary search's time goes. The fix used for the reads of combinator contexts applies: key the views
   by the dependencies and the definitions of the traces (`Context.reads` is keyed by `(deps, bound, chains)`),
   not by the full context, and number bound variables canonically so that renamed contexts share
   (package B of the plan).

## What stands as predicted

The dependency answer (the state trace needs only the counter and the choices, the constraint ranges over
`⌊S⌋`, a projection needs `⌊S⌋` exactly when its component reads another one); the database unchanged apart from
two core facts (`integer_natural`, `maps_identity`); layered components splitting themselves apart by the existing
normalization (an unused `⌊S⌋` is dropped and `counter_def` fires on the projection); the price in time, about
twice on the swap.

## Consequences for the plan

- Rewrite steps S2 to S4 to match the sketch: views with suspension, the closed substitution, no ghost
  components, no derived equations.
- The memo key of the views and one shared suspension facility (`active` of the guard, `projecting` of the
  views) as the first engineering items, with the binary search as the test.
- `consts_choice` and `integer_eq` into the core module; the one-point rule over sequences as an engine item
  next to the triggers.
- The tuple patterns in the lemma language (step S5) remain a convenience: the transpose's lemma shows that
  joint lemmas can be written with the constructor and the selectors.
