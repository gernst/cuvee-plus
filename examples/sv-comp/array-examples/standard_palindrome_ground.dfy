// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_palindrome_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_palindrome_ground.yml (expected: safe), translated from the C
// program by hand: A is filled with arbitrary values, its first half is overwritten by the mirrored second half,
// and then A is a palindrome
//
// findings: the first half is written with reads of the second half, which no iteration writes; the lemma turns
// such a trace into stores of reads of the initial array, given that the reads are outside of the written range,
// which teq.dfy decides as an iteration constraint over a counter; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var A: array<int, int>;
  var i: int;
  var x: int;
  var tmp: int;
  i := 0;
  while i < 100000 {
    tmp := *;
    A := A[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < 50000 {
    A := A[i := A[100000 - i - 1]];
    i := i + 1;
  }
  x := 0;
  while x < 50000 {
    assert A[x] == A[100000 - x - 1];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
