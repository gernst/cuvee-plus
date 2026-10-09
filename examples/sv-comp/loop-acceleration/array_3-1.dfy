// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/array_3-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/array_3-1.yml (expected: safe), translated from the C program by
// hand: A is filled with arbitrary values, and a search for 0 stops at 1023 at the latest by a break, such that i
// is at most 1024
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the search stops by the break at
// 1023 at the latest, which bounds the counter

method main() {
  var A: array<int, int>;
  var i: int;
  var tmp: int;
  i := 0;
  while i < 1024 {
    havoc tmp;
    A := A[i := tmp];
    i := i + 1;
  }
  i := 0;
  while A[i] != 0 {
    if i >= 1024 - 1 {
      break;
    }
    i := i + 1;
  }
  assert i <= 1024;
}

// remaining goals of -teq -simplify:
// none
