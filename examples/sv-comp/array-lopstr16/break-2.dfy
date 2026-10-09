// ./Cuvee.sh -teq -simplify examples/sv-comp/array-lopstr16/break-2.dfy
// SV-COMP ReachSafety-Arrays/array-lopstr16/break-2.yml (expected: safe), translated from the C program by hand:
// the elements are set to 10 up to the middle, where the loop breaks, and they are checked there
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var s: array<int, int>;
  i := 0;
  while i < 1000000 {
    if i > 1000000 / 2 {
      break;
    }
    s := s[i := 10];
    i := i + 1;
  }
  i := 0;
  while i < 1000000 {
    if i <= 1000000 / 2 {
      assert s[i] == 10;
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
