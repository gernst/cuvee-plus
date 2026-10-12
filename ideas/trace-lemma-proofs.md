# Proving and deriving trace lemmas

Status (Oct 12, 2026). The proposal of Oct 10 had three parts: the combinators as recursive definitions over a
data type of traces (an experiment `teq-def.dfy`, since removed), proofs of the database by induction inside
Cuvée with a proof script `{:by ...}` and an automatic tactic, and the derivation of acceleration lemmas by
fusion. The proofs are done differently now: [teq.lean](../resources/cuvee/teq.lean) defines the combinators in
Lean 4 and proves 164 of the 205 lemmas of the database, printed from the modules by `-print lean` (see
[doc/teq.md](../doc/teq.md)); the modules `nested`, `sorting` and `strides` are not proved yet, and the premises
that the Lean proofs needed (dependencies of equal length, indices within the lists, complete guards) are the
well-formedness items of TODO.md. What remains of the proposal is the derivation of lemmas, and induction in the
tool as the general mechanism for user data types.

## Induction in the tool

Induction over traces is structural induction over `Trace = Stop | Step` (a trace taken apart at its last
element, which fits counters: `counter(i, c, n + 1)` unfolds to a `Step`), induction over the dependencies is
induction over sequences by the views `[]` and `ys + [y]`, and induction over the length of a counter is over
`n == 0` and `n + 1`. The same machinery serves user data types: `Rec` represents recursive functions with a
top-level match, `Fuse` already unfolds a case whose pattern matches a constructor, and an induction schema per
`Datatype` with a hypothesis per recursive argument is what is missing. A proof script would name the steps
(`induct n generalizing j; unfold; ih; split; simplify`), a tactic would try the script with the induction
variable taken from the counter among the dependencies and the generalization over the variables of the
observer. The arithmetic side goals (telescoping, `div` and `mod`) contain no traces; whether they go to an
SMT solver or the simplifier learns rounding is undecided. With Lean in place this is no longer needed for the
database; it would be needed for lemmas that users write for their programs, which today are axioms
(see [teq-database.md](teq-database.md)).

## Deriving acceleration lemmas by fusion

An introduction lemma `trace(x, for values do s, v :: s + v) == sums(x, values)`, read from right to left, is
the definition of `sums`, which the database only declares; the acceleration lemmas about `sums` are theorems
about this definition and could be derived instead of written:

- `current(trace(x0, for deps do F))` is the composition of `current` with the fold `trace_F`; fusion
  (`simplify/Fuse.scala`, `g(f(xs), ys)` into `h(xs, ys)`) drives `current` into the cases of the fold and gives
  the plain fold `foldl(F, x0, deps)` without intermediate traces, which is why `current` of every introduced
  function has a closed form at all. `Fuse` needs patterns of views `ys + [y]` for sequences, the accumulator
  position `current(T)` of the recursive call, and lets.
- The fused fold is recognized against the definitions of known functions with a generalized accumulator
  (`h(x, ys + [y]) == h(x, ys) + y` is `x + sum(ys)`; `+ (if y == e then 1 else 0)` is `count`), or against
  templates of closed forms (polynomials in `n` for counters, geometric for products, `if n <= t then p₁(n) else
  p₂(n)` with an unknown threshold for two phases), and the conjecture is proved by induction.
- `earlier` and `prefix` need one general lemma,
  `earlier(j, ⌊trace(x0, for deps do F)⌋) == current(trace(x0, for prefix(j, deps) do F))`, after which the
  earlier-lemma of each introduced function is its current-lemma at `prefix(j, deps)`. These are the free
  theorems of a scan, and the same observation is the lemma schemas of [teq-database.md](teq-database.md):
  one schema per observer replaces `prefix_sums`, `prefix_maxs`, `prefix_counts`, ...
- Where no closed form exists (`maxs`, `mins`), the derived lemmas are invariants: bounds found by abstract
  interpretation of the fused fold (intervals, congruences), proved by induction.
- The same scheme applies to traces that are no introduction lemma yet, e.g. a recurrence over an array
  `b[i := b[k] + G(k)]`, whose read at `j` fuses to `h_j(b0, ys + [k]) == if k + 1 == j then h_k(b0, ys) + G(k)
  else h_j(b0, ys)` and is recognized as `b0[0] + sum(prefix(j, G))` by generalizing over `j`: the lemmas of the
  benchmarks could be synthesized from the programs instead of written, which is the "recurrence solver as a
  lemma generator" of [teq-database.md](teq-database.md).

Limits: recognition is incomplete beyond polynomials and the known functions, fusion requires each step of the
observer to depend on the previous value only (not `invs` over the whole trace, a fold of its own), and the
proofs need `div` and `mod`.

## Open questions

- Should the introduction lemmas become definitions of the functions they name, so that the database splits
  into definitions and derived lemmas? Lean already treats them so.
- Derived lemmas generated at build time into a module, or on demand per program?
- Should sequences get a data type, or stay those of SMT-LIB with the views `[]` and `ys + [y]`?
