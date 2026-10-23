// ./Cuvee.sh -teq -include teq:search -entry find -prove examples/dafny/algorithms/lsearch.dfy
// the first index of x among the first n elements of an array, n if there is none
//
// status: verified with the database alone (Oct 23, 2026, formerly examples/dafny/state, whose version replaced the one
// here with local copies of not_occurs_selects and select_not_occurs_selects of teq:search); it needs no -split

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
