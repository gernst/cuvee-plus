// ./Cuvee.sh -teq -include teq:aggregation -entry main -prove examples/dafny/algorithms/partition.dfy
// the partition of a[0..n) around the pivot a[n - 1] (Lomuto), the inner step of quicksort
//
// status: verified with -teq -simplify; the trace of the array is a conditional swap of the position k with the
// position i, where i is the count of the elements below the pivot so far (the simplifier recognizes the counts);
// the lemmas: the trace is named lomuto with the positions of the swaps as a generic dependency; reads of the
// position k in iteration k are reads of a, since only positions below k are written before (stated on the map that
// counts them, with the named trace as a dependency: a lemma that rewrites the read inside the trace itself does not
// terminate, since it applies again in the update of its own instance); the count is named (below), such that the
// facts of the goal and the side conditions of the lemmas normalize to the same term, as maps are compared literally
// with their bound variables; the result below and from the count on, and the permutation, are rules on the atoms of
// the postcondition; the maps keep the counter of the loop as a further dependency hs, which the lemmas carry
function perm(a: array<int, int>, b: array<int, int>): bool

// the trace of the conditional swaps of the position k with the position i (the number of elements below the pivot so
// far, a further dependency) when a[k] is below the pivot p; the guard reads b[k], which is a[k], since before
// iteration k only positions below k are written
function lomuto(a: array<int, int>, p: int, n: Nat, is: List<int>): Trace<array<int, int>>

lemma {:rw} lomuto_def(a: array<int, int>, p: int, n: Nat, is: List<int>, js: List<int>)
  ensures trace(a, for ⌊counter(0, 1, n)⌋, is, js do b, k, i, j :: case b[k] < p => b[i := b[k]][k := b[i]] case p <= b[k] => b)
    == lomuto(a, p, n, is)

// the elements at the positions k, read in iteration k, are those of a
lemma {:rw} maps_lomuto_read(a: array<int, int>, p: int, n: Nat, is: List<int>, hs: List<int>, P: (int, int, int) -> bool)
  ensures maps(for ⌊counter(0, 1, n)⌋, ⌊lomuto(a, p, n, is)⌋, hs yield k, b, h :: P(b[k], k, h))
    == maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: P(a[k], k, h))

// the number of elements below the pivot among the first n, named, such that the facts of the goal and the side
// conditions of the lemmas normalize to the same term (maps are compared literally, with their bound variables)
function below(a: array<int, int>, p: int, n: Nat, hs: List<int>): int

lemma {:rw} below_def(a: array<int, int>, p: int, n: Nat, hs: List<int>)
  ensures count(true, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: a[k] < p)) == below(a, p, n, hs)

lemma {:rw} below_nonnegative(a: array<int, int>, p: int, n: Nat, hs: List<int>)
  ensures 0 <= below(a, p, n, hs)

lemma {:rw} below_le(a: array<int, int>, p: int, n: Nat, hs: List<int>)
  ensures below(a, p, n, hs) <= integer(n)

// the result: below the number of elements below the pivot, the elements are below it, above, they are not;
// the maps that counts them keeps the counter of the loop as a further dependency hs
lemma {:rw} current_lomuto_below(a: array<int, int>, p: int, n: Nat, hs: List<int>, k: int)
  requires 0 <= k < below(a, p, n, hs)
  ensures (current(lomuto(a, p, n, ⌊counts(0, true, maps(for ⌊counter(0, 1, n)⌋, hs yield k2, h :: a[k2] < p))⌋))[k] < p)
    <==> true

lemma {:rw} current_lomuto_above(a: array<int, int>, p: int, n: Nat, hs: List<int>, k: int)
  requires below(a, p, n, hs) <= k < integer(n)
  ensures (p <= current(lomuto(a, p, n, ⌊counts(0, true, maps(for ⌊counter(0, 1, n)⌋, hs yield k2, h :: a[k2] < p))⌋))[k])
    <==> true

lemma {:rw} perm_lomuto(a: array<int, int>, c: array<int, int>, p: int, n: Nat, is: List<int>)
  ensures perm(current(lomuto(a, p, n, is)), c) <==> perm(a, c)

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

method main(a: array<int, int>, n: int) returns (b: array<int, int>, i: int)
  requires 0 < n
  ensures 0 <= i < n
  ensures forall k: int :: 0 <= k < i ==> b[k] < a[n - 1]
  ensures forall k: int :: i <= k < n - 1 ==> a[n - 1] <= b[k]
  ensures perm(b, a)
{
  var j: int;
  var t: int;
  var pivot: int;
  b := a;
  pivot := a[n - 1];
  i := 0;
  j := 0;
  while j < n - 1
  {
    if b[j] < pivot {
      t := b[i];
      b[i] := b[j];
      b[j] := t;
      i := i + 1;
    }
    j := j + 1;
  }
}
