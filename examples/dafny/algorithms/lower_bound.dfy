// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/lower_bound.dfy
// binary search for the first position of a value at least x in the sorted range a[0..n) (the lower bound): the
// bounds lo and hi are data-dependent, the postcondition relates them to the abstract predicate sorted
//
// status: open, not attempted beyond the goal: lo and hi are traces over each other with the data-dependent guard
// a[(lo + hi) / 2] < x, like bsearch.dfy of examples/dafny/teq, which abstracts the array by partition points for all
// indices; with sorted(a, 0, n) the partition point lb(a, n, x) is meaningful for indices in [0, n) only, so the guard
// lemma (a[m] < x) <==> m < lb(a, n, x) needs 0 <= lo <= hi <= n in the context of the updates, the invariant to be
// established, and bsearch.dfy also needs a cut after the loop

function sorted(a: array<int, int>, lo: int, hi: int): bool

method main(a: array<int, int>, n: int, x: int) returns (lo: int)
  requires 0 <= n
  requires sorted(a, 0, n)
  ensures 0 <= lo <= n
  ensures forall k: int :: 0 <= k < lo ==> a[k] < x
  ensures forall k: int :: lo <= k < n ==> x <= a[k]
{
  var hi: int;
  var mid: int;
  lo := 0;
  hi := n;
  while lo < hi
  {
    mid := (lo + hi) / 2;
    if a[mid] < x {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
}
