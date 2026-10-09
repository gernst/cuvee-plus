// ./Cuvee.sh -teq -simplify examples/sv-comp/array-lopstr16/partial_lesser_bound-1.dfy
// SV-COMP ReachSafety-Arrays/array-lopstr16/partial_lesser_bound-1.yml (expected: safe), translated from the C program by hand:
// the array is set to 0, then the first half to 10, which is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var a: array<int, int>;
  i := 0;
  while i < 10000000 {
    a := a[i := 0];
    i := i + 1;
  }
  i := 0;
  while i < 10000000 / 2 {
    a := a[i := 10];
    i := i + 1;
  }
  i := 0;
  while i < 10000000 / 2 {
    assert a[i] == 10;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
