// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/lower_bound.dfy
// binary search for the first position of a value at least x in the sorted range a[0..n) (the lower bound): the
// bounds lo and hi are data-dependent, the postcondition relates them to the abstract predicate sorted
//
// status: open; an attempt in the style of merge.dfy (the guard a[(lo + hi) / 2] < x higher-order and pinned, the
// trace of hi tied by an open trace variable, the exit hi <= lo as a side condition on the current values, the
// result the abstract lower bound lb(a, n, x) with its properties as rules on the atoms of the postcondition) does
// not terminate once the exit condition current(Hv) <= current(Lv) is present (its decision rewrites current(Lv) by
// the same lemma, re-entrant), and terminates with the goal open without it; the runs of Oct 10 reported the
// timeouts as proofs (NOTES.md, finding 18)

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
