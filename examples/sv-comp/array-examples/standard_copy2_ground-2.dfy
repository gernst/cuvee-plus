// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_copy2_ground-2.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_copy2_ground-2.yml (expected: safe), translated from the C program by hand:
// an arbitrary array is copied twice, and the last copy is checked to agree with it (standard_copy4 to _copy9
// are variants with more copies)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var x: int;
  var v: int;
  var a1: array<int, int>;
  var a2: array<int, int>;
  var a3: array<int, int>;
  i := 0;
  while i < 100000 {
    v := *;
    a1 := a1[i := v];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    a3 := a3[i := a2[i]];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a1[x] == a3[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
