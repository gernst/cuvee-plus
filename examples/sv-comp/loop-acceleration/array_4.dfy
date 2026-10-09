// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/array_4.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/array_4.yml (expected: safe), translated from the C program by hand:
// the array is arbitrary but for a 0 at its last position 1023, and the search for the first 0 stops at most there,
// which is checked
//
// findings: the search for 0 runs over the array with 0 stored at 1023; a lemma states that the iteration
// constraint that the elements before n differ from v holds iff n <= c and those of the array without the store
// differ; closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1024

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>

// a search for v that runs over an array with v stored at c >= 0 stops at c at the latest: the iteration constraint
// that the elements differ from v before n holds iff n <= c and the elements of the array without the store differ
// from v before n (with a further dependency hs)
lemma {:rw} {:free} {:teq} forall a: array<int, int>, c: int, v: int, n: int, hs: seq<int> ::
  if 0 <= c
  then invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: a[c := v][k] != v)
    <==> n <= c && invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: a[k] != v)

method main() {
  var N: int;
  var i: int;
  var v: int;
  var A: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N - 1 {
    v := *;
    A := A[i := v];
    i := i + 1;
  }
  A := A[N - 1 := 0];
  i := 0;
  while A[i] != 0 {
    i := i + 1;
  }
  assert i <= N;
}

// remaining goals of -teq -simplify:
// none
