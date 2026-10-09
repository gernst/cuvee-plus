// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_copy3_ground-1.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_copy3_ground-1.yml (expected: safe), translated from the C program by hand:
// an arbitrary array is copied three times, and the last copy is checked to agree with it
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var x: int;
  var v: int;
  var a1: array<int, int>;
  var a2: array<int, int>;
  var a3: array<int, int>;
  var a4: array<int, int>;
  i := 0;
  while i < 100000 {
    havoc v;
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
  i := 0;
  while i < 100000 {
    a4 := a4[i := a3[i]];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a1[x] == a4[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
