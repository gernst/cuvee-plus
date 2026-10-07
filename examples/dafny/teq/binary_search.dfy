// an index of x among the first n elements of a sorted array, -1 if there is none

method search(a: array<int, int>, n: int, x: int) returns (i: int)
  requires 0 <= n
  requires forall j: int, k: int :: 0 <= j <= k < n ==> a[j] <= a[k]
  ensures 0 <= i ==> i < n && a[i] == x
  ensures i < 0 ==> forall k: int :: 0 <= k < n ==> a[k] != x
{
  var lo: int;
  var hi: int;
  var mid: int;
  lo := 0;
  hi := n;
  i := -1;
  while lo < hi && i < 0
  {
    mid := (lo + hi) / 2;
    if a[mid] < x {
      lo := mid + 1;
    } else if x < a[mid] {
      hi := mid;
    } else {
      i := mid;
    }
  }
}
