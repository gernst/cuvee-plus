// ./Cuvee.sh -teq -include teq:aggregation -entry main -prove examples/dafny/algorithms/partition.dfy
// the partition of a[0..n) around the pivot a[n - 1] (Lomuto), the inner step of quicksort
//
// status (Oct 16, 2026): verified with -teq -prove; a wrong postcondition, the lower region up to i inclusive or
// perm(b, a[0 := 1]), leaves a goal; b and i read each other, hence -teq makes them one trace of (b, i, j) with the
// scan j; the count i is summarized through the view of its component (lomuto_def on the array component, whose read
// of the position in iteration k is a read of a, maps_lomuto_read, and the count named below); the two regions of the
// result are rules on the atoms of the postcondition over the whole trace of (b, i, j) (partition_below,
// partition_above), since a summary of the array component with the positions j stated as a counter is not matched
// (the matcher pairs the component's dependency ⌊S⌋.2 only with a generic list); the bound i <= j is stated with
// n' == natural(j), as -teq relates the number of iterations and j only by it (below_le_natural)

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
function {:fold} below(a: array<int, int>, p: int, n: Nat, hs: List<int>): int
{
  count(true, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: a[k] < p))
}

lemma {:rw} below_nonnegative(a: array<int, int>, p: int, n: Nat, hs: List<int>)
  ensures 0 <= below(a, p, n, hs)

// the bound below_le for a number of iterations n == natural(m), as -teq relates it to the final value m of the
// scan, which the arithmetic does not resolve into integer(n) == m
lemma {:rw} below_le_natural(a: array<int, int>, p: int, n: Nat, hs: List<int>, m: int)
  requires n == natural(m) && 0 <= m
  ensures below(a, p, n, hs) <= m <==> true

// the result on the whole state trace of (b, i, j): below the number of elements below the pivot, the elements are
// below it, from there up to n, they are not
lemma {:rw} partition_below(a: array<int, int>, p: int, n: Nat, k: int)
  requires 0 <= k < below(a, p, n, ⌊counter(0, 1, n)⌋)
  ensures (current(trace(a, 0, 0, for ⌊counter(0, 1, n)⌋ do b, i, j, kk ::
                     case b[j] < p => b[i := b[j]][j := b[i]] case p <= b[j] => b,
                     case b[j] < p => i + 1 case p <= b[j] => i,
                     j + 1)).0[k] < p) <==> true

lemma {:rw} partition_above(a: array<int, int>, p: int, n: Nat, k: int)
  requires below(a, p, n, ⌊counter(0, 1, n)⌋) <= k < integer(n)
  ensures (p <= current(trace(a, 0, 0, for ⌊counter(0, 1, n)⌋ do b, i, j, kk ::
                     case b[j] < p => b[i := b[j]][j := b[i]] case p <= b[j] => b,
                     case b[j] < p => i + 1 case p <= b[j] => i,
                     j + 1)).0[k]) <==> true

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
