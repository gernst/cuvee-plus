# Conditional stores instead of cases

A loop body with s conditional stores, each choosing a value by a guard that
does not depend on the iteration, becomes an update with 2^s cases, one per
path of the symbolic execution of `-teq`, e.g. the MonoCera benchmarks
`pr3`-`pr5` (see [benchmarks/monocera/summary.md](../benchmarks/monocera/summary.md)):

```
trace(a0, for ⌊counter(0, 1, n)⌋ do a, k ::
  case 7 >= m && 3 >= m => a[2 * k := 7][2 * k + 1 := 3]
  case 7 >= m && !(3 >= m) => a[2 * k := 7][2 * k + 1 := 0]
  case !(7 >= m) && 3 >= m => a[2 * k := 0][2 * k + 1 := 3]
  case !(7 >= m) && !(3 >= m) => a[2 * k := 0][2 * k + 1 := 0])
```

The same update with conditional values has a single case, which the
lemmas on strided stores without cases match (`strides.dfy`):

```
trace(a0, for ⌊counter(0, 1, n)⌋ do a, k ::
  a[2 * k := if 7 >= m then 7 else 0][2 * k + 1 := if 3 >= m then 3 else 0])
```

The sequences of conditionals that overflow the stack in `-teq` (2^10 paths
of `diamond_2-2`, see TODO.md) and part of the 140 Loops tasks that end with
"rewriting does not terminate" at 15 min (SV-COMP.md) presumably have the same
cause.

## Not as a rewrite rule (experiment, Oct 11, 2026)

The merge was tried as a lemma of the database, included with `-include`
together with the declarations of `teq.dfy` that it needs:

```
lemma {:rw} trace_merge_store(a0: array<int, int>, n: Nat, P: bool, X: int, Y: int, E: (int) -> int)
  ensures trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: case P => a[E(k) := X] case !P => a[E(k) := Y])
    == trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: a[E(k) := if P then X else Y])
```

- With a single conditional cell (two cases), it applies and the equation of
  the two forms is proved.
- With two cells (the example above), it does not apply: `Rewrite.matchesUpdates`
  needs one substitution under which every case of the update is covered by a
  case of the pattern, and a pattern with two cases cannot cover four cases
  pairwise. A rule would be needed per number of cells, and per order of the
  guards.
- The simplifier already prunes the cases: guards over the same variable are
  normalized into intervals, which leaves 3 instead of 4 cases
  (`m <= 3`, `3 < m <= 7`, `7 < m`). This does not help a rule that expects
  the product form.
- Joins of two guarded stores were left out of the database before, since a
  pattern with two cases also matches an update with one case and leaves the
  variables of the other case free (see TODO.md and doc/teq.md).

## Where else

1. **In `-teq`:** the symbolic execution of the loop body keeps a conditional
   whose branches only store at the same index into a store of a conditional
   value, instead of splitting the path. This avoids the 2^s paths in the
   first place (and the stack overflow), but only for conditionals of this
   shape; the TEQ transform would need to compare the indices of the branches
   syntactically.
2. **As a step of the simplifier** that normalizes the cases of an update
   (`Eps`): cases whose bodies are the same stores up to the stored values
   merge pairwise into one case with conditional values, iterated by the outer
   loop. Each step is local to the `Eps` and needs no matching. It must not
   undo other normalizations of guards, and the merged values must be
   simplified under the guard of the merged case.

The first is presumably cheaper and suffices for the benchmarks; the second
also catches cases that arise after other rewrites. Neither is implemented.
