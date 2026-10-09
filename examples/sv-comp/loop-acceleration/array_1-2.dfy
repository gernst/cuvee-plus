// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/array_1-2.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/array_1-2.yml (expected: safe), translated from the C program by
// hand: A[i] is set to i for i below 1024, and A[1023] is 1023
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var A: array<int, int>;
  var i: int;
  i := 0;
  while i < 1024 {
    A := A[i := i];
    i := i + 1;
  }
  assert A[1023] == 1023;
}

// remaining goals of -teq -simplify:
// none
