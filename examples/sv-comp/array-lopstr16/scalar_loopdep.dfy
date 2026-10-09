// ./Cuvee.sh -teq -simplify examples/sv-comp/array-lopstr16/scalar_loopdep.dfy
// SV-COMP ReachSafety-Arrays/array-lopstr16/scalar_loopdep.yml (expected: safe), translated from the C program by hand:
// a[i] = y, where y counts up from 100, and a[i] >= 100 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var x: int;
  var y: int;
  var a: array<int, int>;
  y := 100;
  i := 0;
  while i < 100000 {
    x := y;
    a := a[i := y];
    y := y + 1;
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    assert a[i] >= 100;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
