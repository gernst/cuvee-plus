// ./Cuvee.sh -teq -include teq:search -include teq:sorted -prove examples/dafny/state/lower_bound.dfy
// the lower bound of x in a sorted array, after examples/dafny/algorithms/lower_bound.dfy (open under -teq -simplify):
// the binary search without the found case, whose result is the partition point lower(a, n, x); proved with the
// named bisection of examples/dafny/algorithms/bsearch.dfy (package O of doc/prove.md): the guard of the else branch,
// !(a[mid] < x), is normalized to x <= a[mid], whose negation is a[mid] < x again, so its cut is lower(a, n, x) by
// cut_lower, and the reads of that form get their own rule (lower_le); the exit hi <= lo with
// lo <= lower(a, n, x) <= hi makes lo the partition point, which closes both quantified postconditions by the rules
// on sortedness

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
