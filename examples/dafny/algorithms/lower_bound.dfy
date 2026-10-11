// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/lower_bound.dfy
// binary search for the first position of a value at least x in the sorted range a[0..n) (the lower bound): the
// bounds lo and hi are data-dependent, the postcondition relates them to the abstract predicate sorted
//
// status: open; an attempt in the style of merge.dfy (the guard a[(lo + hi) / 2] < x higher-order and pinned, the
// trace of hi tied by an open trace variable, the exit hi <= lo as a side condition on the current values, the
// result the abstract lower bound lb(a, n, x) with its properties as rules on the atoms of the postcondition) closes
// the goal when the exit is a comparison h <= l of two open variables matched against the fact hi <= lo, and the
// properties then close the postconditions on lb(a, n, x) (Oct 11, 2026, evening); but h and l are not tied to the
// traces there, so the rule is not sound as a lemma, and every sound tie fails for reasons of the engine (NOTES.md):
// a condition l == current(Lv) with Lv bound is simplified before it is decided or matched, which rewrites
// current(Lv) by the lemma itself (re-entrant, no termination); with Lv open the condition binds Lv, but the
// left-hand side current(trace(0, for ⌊counter(0, 1, nn)⌋, hs do ...)) matched against current(Lo) through the
// definition of the trace variable Lo leaves nn and hs unbound, and the trace condition that would bind them no
// longer matches once Lv is bound; the runs of Oct 10 reported the timeouts as proofs (NOTES.md, finding 18)

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
