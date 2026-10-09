// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_sentinel-2.dfy
// SV-COMP array-examples/standard_sentinel-2.yml (expected: safe), translated from the C program
// by hand: a is filled with arbitrary values, a marker is placed at a position pos inside the array, and the search
// for the marker, which has no bound, stops at pos at the latest
//
// findings: as standard_find_ground-1, with reads of the array instead of a sequence: the iteration constraint of
// the unbounded search becomes !occurs(e, selects(a, ⌊counter(0, 1, n)⌋)) by not_occurs_selects_def of teq.dfy, and
// a lemma concludes n <= j from a[j] == e for the marker at pos; its left-hand side n <= j is a comparison, which terminates now, since its side
// condition is an atom matched against the facts; closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// the iteration constraint of the search, the elements of a at the iterations 0, ..., n - 1 differ from e, is
// !occurs(e, selects(a, ⌊counter(0, 1, n)⌋)) by not_occurs_selects_def of teq.dfy; then a position j where e is found
// is not before n, a comparison as the left-hand side, which terminates, since its side condition is an atom that is
// matched against the facts, not an iteration constraint
lemma {:rw} {:teq} lemma_1(n: Nat, j: int, e: int, a: array<int, int>)
  requires !occurs(e, selects(a, ⌊counter(0, 1, n)⌋)) && a[j] == e && 0 <= j
  ensures integer(n) <= j

method main() {
  var N: int;
  var a: array<int, int>;
  var marker: int;
  var pos: int;
  var i: int;
  var tmp: int;
  assume 0 < N;
  marker := *;
  pos := *;
  i := 0;
  while i < N {
    tmp := *;
    a := a[i := tmp];
    i := i + 1;
  }
  if pos >= 0 && pos < N {
    a := a[pos := marker];
    i := 0;
    while a[i] != marker {
      i := i + 1;
    }
    assert i <= pos;
  }
}

// remaining goals of -teq -simplify:
// none
