// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_init2_ground-2.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_init2_ground-2.yml (expected: safe), translated from the C program by hand:
// the array is set to 42 and then to 43, which is checked (standard_init3 to _init9 are variants with more
// loops)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var x: int;
  var a: array<int, int>;
  i := 0;
  while i < 100000 {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    a := a[i := 43];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a[x] == 43;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
