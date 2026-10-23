// ./Cuvee.sh -teq -include teq:search -include teq:sorted -prove examples/dafny/algorithms/bsearch.dfy
// binary search over a sorted array, proved by a lemma over the whole cycle (package O of doc/prove.md): the array,
// its bound and the key are parameters, the array is sorted, sorted(a, 0, n); the variants with partition points,
// the probe lo + (hi - lo) / 2, and two layers of per-component abstractions were removed (Oct 23, 2026)
//
// sortedness is used where the reads of the array become comparisons of the index with the partition points
// lower(a, n, y) and upper(a, n, y), which exist for a sorted array, for indices within a[0..n) only; lo and hi read
// each other and form one trace S of two accumulators, which bisection folds: a bisection of [l0, h0) with
// a probe strictly inside the interval, (lo + hi) / 2 here; if its guards G and H hold on a prefix and a suffix, lo
// stays below the cut of G and hi above the cut of the negation of H (bisection_lo, bisection_hi, forward facts at
// current(S).0 and current(S).1); the conditions are decided by the rules on sortedness within the range of their
// premise and, for the probe, by the bounds of division in the linear arithmetic; the cuts of the comparisons with x
// are the partition points (cut_lower, lower_succ)

method search(a: array<int, int>, n: int, x: int) returns (i: int)
  requires 0 <= n && sorted(a, 0, n)
  ensures 0 <= i ==> i < n && a[i] == x
  ensures i < 0 ==> forall k: int :: 0 <= k < n ==> a[k] != x
{
  var lo: int;
  var hi: int;
  var mid: int;
  lo := 0;
  hi := n;
  i := -1;
  while lo < hi
  {
    mid := (lo + hi) / 2;
    if a[mid] < x {
      lo := mid + 1;
    } else if x < a[mid] {
      hi := mid;
    } else {
      i := mid;
      break;
    }
  }
}
