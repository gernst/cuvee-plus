# Multisets for folds that do not depend on the order

A design over the multisets of the core (cvc5's bags), implemented in part (Oct 27, 2026) as the module `teq:multisets`
(resources/cuvee/teq/multisets.dfy; doc/teq.md): `elems`, `msum`, `mparity`, `mmax`, `mmin`, the multiplicities, the
conversions of the sums and parities of reads at keys, swap and shift of arrays; in `-svcomp` since 0.52.17.
Measured (cloud, Oct 27, with the lengths of the choice lists of 0.52.16): converting the folds of all lists
(`sum(xs) == msum(elems(xs))`, `count`, `current(maxs(...))`) proves the 10 sums and averages of reducercommutativity and
mapsum, mapavg (+18 on Arrays), but loses 7 of Arrays (the maxima of standard_maxInArray_ground, ms2-ms5) and 27 of Loops
(sqrt1, ps2-ps6, ...): rewriting is innermost, so a conversion of the inner fold preempts the rules of teq:aggregation
on the comparisons around it. Considered next: the
multisets as a detour for permutations only, converted back afterwards; the conversion back loops with the forward one
where a permutation lemma fails. In progress instead (Oct 28, uncommitted): the twins of the lemmas of teq:aggregation
that consume a fold of a list (`sum_consts`, `sum_counter`, the counts, the bounds of the maxima and minima, the updates
of selects), the same statements on the folds of multisets, so that the conversion of all folds preempts none of them;
locally standard_maxInArray_ground and sqrt1-ll are proved again; its forward lemmas have no twins. Open as well: sep
(C's `%` keeps the sign, so the loop is a count by a predicate, no `parity`), the bitwise reductions (no folds yet), and
the Lean model of the multisets (the module is not in `MODULES` of generate.py). The folds of the database over lists (`sum`, `parity`, `count`, the maxima
and minima, the bitwise reductions of C) are stated over lists, so a permutation of an array (a swap, a rotation) is
invisible only through one lemma per fold and per kind of permutation. A multiset of the values separates the two: a
fold that does not depend on the order is a function of the multiset, and a permutation preserves the multiset.

## The tasks

reducercommutativity (28 tasks: avg, max, rangesum, sep, sum, each for N = 5 to 60 and unbounded) and array-crafted
bAnd, bor, xor (15): a reduction `R` over `x[0..N)` of nondeterministic values is computed three times, on the input,
after `x[0]` and `x[1]` are swapped, and after the array is rotated by one (a shift loop `x[i] = x[i + 1]` for
`i < N - 1`, then `x[N - 1] = temp`), and the three results must be equal. None is solved (cloud, 0.52.14).

- sum, avg (`sum / N`): `sum`; sep: `parity` (+1 for an even element, -1 for an odd one); max: the maximum from the
  seed 0 (`ret = ret < x[i] ? x[i] : ret`); bAnd, bor, xor: `bitand`, `bitor`, `bitxor`, uninterpreted functions of
  the C prelude.
- rangesum sums `x[N/2 + 1 .. N)` only: expected false, since the subrange is not invariant under the permutations;
  the design must not prove it.

The remaining goal of sum05-2 (0.52.14 with the update lemmas, `-print dfy`): the swap is decided already, open is the
rotation, `sum(selects(x₅₆, ⌊K₁₆⌋))` over `x₅₆ == current(trace(x₂₁[0 := earlier(1, Tmp?₁₃)][1 := earlier(0,
Tmp?₁₃)], for ⌊K₅₃⌋ do x₄₉, k₅₂ :: x₄₉[k₅₂ := x₄₉[k₅₂ + 1]]))` with the store of the old first element at the end.

## Not taken

- Splitting lists into slices (`sum(prefix(n, xs))` split at a position, sums of selects over subranges as sums of
  slices): rejected by decision.
- One lemma per fold and per permutation (swap, rotation for each of seven folds): fourteen rules of a very specific
  shape (the rotation is a whole loop plus a store), and every new fold or permutation multiplies them.
- `perm(a, b)` of sorted.dfy: a bijection of all integers, and a fact the goal does not contain, so a rule would have
  to bind `b` from facts that are not there; the rules need a direction, which the multiset gives (towards the
  original array).

## The multisets of the core

The core has finite multisets already, cvc5's bags (`Bag`, `Fun.bag`, declared in resources/cuvee/smtlib/prelude.smt2:
`bag.empty`, `bag`, `bag.union_disjoint`, `bag.difference_subtract`, `bag.count`, `bag.card`, ...), which the Dafny
frontend reads and prints as `multiset<a>`, `multiset{a, b}`, `+`, `-`, `m[x]` and `|m|`. A new optional module
`teq:bags` over teq.dfy adds only the multiset of a list and the folds of multisets:

```
// the multiset of the elements of a list, the counterpart of Dafny's multiset(s) for the lists of the database (a
// datatype, not seq; the frontend does not parse multiset(s) either, TODO.md); two lists have the same one exactly if
// one is a permutation of the other
function {:rw} {:teq} elems<a>(xs: List<a>): multiset<a>
{
  match xs
  case nil => multiset{}
  case cons(y, ys) => multiset{y} + elems(ys)
}

// the folds of a multiset, for the folds of lists that do not depend on the order; without body, since a multiset
// has no structural recursion, and characterized by the conversions below
function {:teq} msum(m: multiset<int>): int
function {:teq} mparity(m: multiset<int>): int
function {:teq} mmax(seed: int, m: multiset<int>): int
function {:teq} mmin(seed: int, m: multiset<int>): int
function {:teq} mand(m: multiset<int>): int     // and likewise mor, mxor, over bitand, bitor, bitxor
```

(`count(e, xs)` is the multiplicity `elems(xs)[e]` and needs no fold of its own; `count_selects_elems` is that equation.) `elems` unfolds only on constructors,
like the other functions of lists, so `elems(selects(a, ⌊counter(0, 1, n)⌋))` stays as it is. The simplifier treats
the operations on bags as uninterpreted (no normal form of `+` on multisets); the design does not need one, since
the lemmas rewrite whole multisets of permuted arrays back to those of the original.

## The lemmas

Three groups; the first two are the whole cost of a new fold or a new permutation.

**A fold that does not depend on the order is a fold of the multiset** (one per fold, on the values read at keys only,
where permutations occur):

```
lemma {:rw} {:teq} sum_selects_elems(a: array<int, int>, keys: List<int>)
  ensures sum(selects(a, keys)) == msum(elems(selects(a, keys)))
```

and `parity_selects_elems`, `count_selects_elems`, the maxima (`current(maxs(c, selects(a, keys)))` and the
conditional form of the loop of max), `bitand`/`bitor`/`bitxor` over their folds (`bitands`, `bitors`, `bitxors` of
ideas/array-lemmas.md, the traces `r := bitand(r, x[i])` folded first). Stated last in their modules, so that the
lemmas on lists apply first (the update lemmas `sum_selects_update`, the sums over counters).

**A permutation of the range preserves the multiset** (one per kind of permutation, for all folds at once):

```
// a swap of two positions inside the keys, with the values written as reads of the array, as the simplifier
// leaves them (the values as conditions, since the reads are evaluated before the lemma matches)
lemma {:rw} {:teq} elems_selects_swap(a: array<int, int>, p: int, q: int, v: int, w: int, keys: List<int>)
  requires distincts(keys) && occurs(p, keys) && occurs(q, keys) && v == a[q] && w == a[p]
  ensures elems(selects(a[p := v][q := w], keys)) == elems(selects(a, keys))

// a rotation by one over i, ..., i + n: the shift of the loop, then the old first element at the end
lemma {:rw} {:teq} elems_selects_rotate(a: array<int, int>, i: int, n: int, v: int)
  requires 0 <= n && v == a[i]
  ensures elems(selects(current(trace(a, for ⌊counter(i, 1, n)⌋ do x, k :: x[k := x[k + 1]]))[i + n := v],
                      ⌊counter(i, 1, n + 1)⌋))
    == elems(selects(a, ⌊counter(i, 1, n + 1)⌋))
```

and the reverse loops (`x[k] := x[k - 1]` from the end) as they occur. The conditions on the values are closed side
conditions, decided by the reads of the context (`earlier(1, Tmp?)` against `x₂₁[1]`).

**Folds of multisets that the goal compares** are equal terms once their multisets are: `msum(elems(selects(x, ⌊K⌋)))` on both
sides of `ret == ret5` is decided syntactically. Nothing else is needed for the reducer tasks; avg is the same sum
divided by `N`.

## Order of application

The conversion to multisets must not change the shape of sums elsewhere: the rules on lists (the update lemmas, sums over
counters, `sum_selects_cons` of the examples) come first in the file, the conversion last, so it applies only to a
`sum(selects(...))` that nothing else rewrites. Rewriting is innermost, so the swap and the rotation inside the
argument are rewritten (or not) before the conversion; the lemmas on multisets then match `elems(selects(...))` of the
permuted array. Risk: a sum that the list rules would have rewritten later, after a fact is known, is a fold of a multiset already;
measure on the tasks with sums over arrays (MonoCera-Sum, array-crafted zero_sum, the prefix sums of
examples/dafny/algorithms).

## Lean

Core only (no Mathlib), but `List.Perm` is in core: generate.py maps the bags of the core once, `Bag a` to the
quotient of `List a` by `List.Perm` (`Quotient (List.isSetoid a)`), `multiset{}`, `multiset{y}`, `+` and `m[x]` to
the lifted nil, singleton, append and count; `elems xs` is the class of `xs`, and each fold of multisets is lifted
from the fold of lists through `Quotient.lift`, with the proof that the fold respects permutations (by commutativity
and associativity of its operator). `bitand`, `bitor`, `bitxor` are uninterpreted in Cuvée; their folds need
commutativity and associativity as axioms of the model (true of the C operators), stated once. The swap and rotation
lemmas are `List.Perm` facts about `selects`.

## What it does not solve

array-patterns (TODO.md): the two arrays of a task are written in lockstep from equal initial contents, and their
sums are related by a pointwise invariant (`array2[N - 1 - j] == -array1[j]`), not by a permutation of one array;
the multiset of a single array after stores at repeating keys has no closed form either. Multisets would make the reindexing
part of a lockstep lemma unnecessary, not the invariant.

## Steps

1. `teq:bags` with `elems`, `msum`, `sum_selects_elems`, `elems_selects_swap`, `elems_selects_rotate`; check on
   sum05-2 and avg05-1 (`-print dfy`), then rangesum05 (must stay unproved).
2. The other folds: parity (sep), max, the bitwise folds with their trace folds; Lean model and proofs (sub-agent).
3. One cloud run of Arrays and Loops: no task lost, in particular the sums of MonoCera and array-crafted.
4. doc/teq.md (the module), TODO.md, and this file removed once documented.
