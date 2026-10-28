# Conditional stores instead of cases

**Status (Oct 28, 2026): history, not taken.** The merge of guarded stores into stores of conditional values was
rejected by decision (only cases with equal results merge); the shape lemmas per number of cases described below
were replaced in 0.53.1 by the folds `strides₂` to `strides₅` with one list of values per cell, synthesized per case
by the matcher ([cases-and-folds.md](cases-and-folds.md)). Kept for the experiments and the reasons.

**The cases in the synthesized maps (Oct 28, 2026, implemented; on the cloud from 0.53.6 on, pr3-pr5, pnr2, pnr3 proved by 0.53.10).** Neither a merge in the simplifier
nor a lemma per number of cases: the strided stores are the folds `strides₂` to `strides₅` with one list of values per
cell (strides.dfy), and the matcher matches a pattern without cases against the cases of an update one by one, where
the bound variables of the synthesized dependencies take a value per case and the map gets the cases of the update
(`Rewrite.update`, doc/prove.md). The trace keeps its cases; they move into the lists of values. This applies to all
folds over dependencies, so `stores` also takes conditional stores at the same key; whether that preempts the
conditional-store lemmas below is what the cloud run has to show. The sections below are the history.

**A generic lemma over the window of an iteration (Oct 28, 2026, measured, not adopted).** A loop whose iteration k
changes only the cells of its window, with values that do not depend on the array, by any number of cases, leaves at
j the value that the iteration j / s stores there; the update is a higher-order variable `U`, the window a quantified
side condition:

```
lemma {:rw} {:teq} select_current_trace_window2(a0: array<int, int>, n: int, j: int, U: (array<int, int>, int) -> array<int, int>)
  requires forall b: array<int, int>, k: int, i: int :: i != 2 * k && i != 2 * k + 1 ==> U(b, k)[i] == b[i]
  requires forall b: array<int, int>, c: array<int, int>, k: int :: U(b, k)[2 * k] == U(c, k)[2 * k] && U(b, k)[2 * k + 1] == U(c, k)[2 * k + 1]
  ensures current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: U(a, k)))[j]
    == if 0 <= j < 2 * n then U(a0, j / 2)[j] else a0[j]
```

It needs one engine step to decide its conditions, either a read of a choice as the choice of the reads
(`Simplify.select`) or the choices lifted out of the atoms like `ite` (`Normalize.choices`, applied in `Rewrite.holds`
after simplification); both keep the cases. It works in principle: a goal of the shape of pr2 in isolation in 3 s, pr2 in
46 s (10 s with the shape lemma). But its pattern matches every trace of an array over a counter, whose quantified
conditions are then evaluated at every read; pr3 and nr2 do not finish in 90 s. A cheap first condition that recognizes
an update writing only its window, decided from its shape, would make it the principled form; by decision (Oct 28), the
module took shapes per number of cases instead, removed in 0.53.1 (`select_current_trace_stride3_cases4` to `stride5_cases6`,
`select_current_trace_stride2_defaults`): pr3 (55 s) and pnr2 (73 s) proved on the cloud at 120 s, pr4 at the limit of
120 s, pr5 in 485 s (within the 15 min of the competition). Rejected by decision (Oct 27,
2026): merging the cases in the simplifier (`Simplify.eps`), even restricted to chains of stores at the same indices
whose values do not read the array; only cases with equal results are merged, since the case distinction of an update
is what the lemmas match. Measured before the decision: pr3 proved, rew and ms2 lost (a store of a choice of arrays,
and a reset and an accumulation at one cell merged into one value).

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
lemma {:rw} trace_merge_store(a0: array<int, int>, n: int, P: bool, X: int, Y: int, E: (int) -> int)
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

## The same gap for a single store per iteration

The engine has no join of guarded stores at all, also where one store per iteration would fold into `stores`, and
the lemmas of the database work around it shape by shape (arrays.dfy):

- `select_current_trace_conditional_store` and its variant `_deps` (copysome1-1, array_mul_init, motivex): the update
  `case C(k) => a[k := V(k)] case !C(k) => a` has a case that keeps the array, which is no store, so the fold
  `stores` does not match. Joined into `a[k := if C(k) then V(k) else a[k]]`, the general mechanism would apply:
  `trace_read_initial` turns the read `a[k]` into the initial `a0[k]` (the keys of a counter are distinct), the trace
  folds into `stores(a0, ⌊counter(0, 1, n)⌋, maps(...))` with the values synthesized as a map, and `current_stores`
  with the lemmas on counters gives the read at `j`, which is the right-hand side of the lemma. The same holds for
  `select_current_trace_cap` (condn) and `select_current_trace_reset_keep` (ms1).
- `stores_cases` (conda, s1lif-s5lif) is that chain for two stores by cases on the old value, `case P(a[k]) =>
  a[k := c] case !P(a[k]) => a[k := G(a[k])]`, and needs a second gap closed as well: its first case stores a
  constant `c`, since a higher-order variable is only instantiated by an abstraction of a term that occurs
  (`Rewrite.abstraction`), so `F(a[k])` cannot be the constant function; with constant abstractions, one lemma with
  `F` and `G` would cover both cases, but `trace_read_initial` would then match every trace of stores at distinct
  keys (`f = z => v`) and rewrite it to itself.
- `stores_index_cases` (brs2-brs5) is the same with guards on the index.

A join as a step of the engine (the second variant above) would make these six lemmas derived.

