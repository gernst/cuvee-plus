// ./Cuvee.sh -teq -split -simplify examples/dafny/teq/lsearch.dfy
// the first index of x among the first n elements of an array, n if there is none
//
// status: verified with -teq -split -simplify by not_occurs_selects_def and select_not_occurs_selects of teq.dfy;
// without -split, the disjunction of the exits remains, which holds by a case split on a[i] == x

method find(a: array<int, int>, n: int, x: int) returns (i: int)
  requires 0 <= n
  ensures 0 <= i <= n
  ensures i < n ==> a[i] == x
  ensures forall k: int :: 0 <= k < i ==> a[k] != x
{
  i := 0;
  while i < n && a[i] != x
  {
    i := i + 1;
  }
}
