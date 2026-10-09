// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/array_4.dfy
// SV-COMP loop-acceleration/array_4.yml (expected: safe), translated from the C program by hand:
// the array is arbitrary but for a 0 at its last position 1023, and the search for the first 0 stops at most there,
// which is checked
//
// findings: the search for 0 runs over the array with 0 stored at 1023; the iteration constraint becomes
// !occurs(0, selects(...)) by not_occurs_selects_def of teq.dfy, and a lemma states that it holds for the array with
// the store iff n <= c and for the array without it; closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1024

// a search for v that runs over an array with v stored at c >= 0 stops at c at the latest: the iteration constraint
// that the elements differ from v before n, which is !occurs(v, selects(...)) by not_occurs_selects_def of teq.dfy,
// holds iff n <= c and the elements of the array without the store differ from v before n
lemma {:rw} {:teq} lemma_1(a: array<int, int>, c: int, v: int, n: Nat)
  requires 0 <= c
  ensures !occurs(v, selects(a[c := v], ⌊counter(0, 1, n)⌋))
    <==> integer(n) <= c && !occurs(v, selects(a, ⌊counter(0, 1, n)⌋))

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
