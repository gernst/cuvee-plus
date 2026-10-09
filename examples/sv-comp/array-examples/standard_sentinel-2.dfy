// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_sentinel-2.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_sentinel-2.yml (expected: safe), translated from the C program
// by hand: a is filled with arbitrary values, a marker is placed at a position pos inside the array, and the search
// for the marker, which has no bound, stops at pos at the latest
//
// findings: as standard_find_ground-1, with reads of the array instead of a sequence: the iteration constraint of
// the unbounded search is abstracted by the auxiliary predicate absent(n, a, e), and a lemma concludes n <= j from
// a[j] == e for the marker at pos; its left-hand side n <= j is a comparison, which terminates now, since its side
// condition is an atom matched against the facts; closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>

// e does not occur in the array a at the positions 0, ..., n - 1, an auxiliary predicate, which is not defined
predicate absent(n: int, a: array<int, int>, e: int)

// the iteration constraint of a search, the elements of a at the iterations 0, ..., n - 1 differ from e, states that
// e is absent there; then a position j where e is found is not before n, a comparison as the left-hand side, which
// terminates, since its side condition is an atom that is matched against the facts, not an iteration constraint
lemma {:rw} {:free} {:teq} forall n: int, e: int, a: array<int, int>, hs: seq<int> ::
  invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: a[k] != e) <==> absent(n, a, e)
lemma {:rw} {:free} {:teq} forall n: int, j: int, e: int, a: array<int, int> ::
  if absent(n, a, e) && a[j] == e && 0 <= j
  then n <= j

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
