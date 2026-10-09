// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_copy7_ground-1.dfy
// SV-COMP array-examples/standard_copy7_ground-1.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of standard_copy1_ground-1 with other constants or assertions; checks
// a1[x] == a8[x]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var tmp₂: int;
  var a1: array<int, int>;
  var a2: array<int, int>;
  var a3: array<int, int>;
  var a4: array<int, int>;
  var a5: array<int, int>;
  var a6: array<int, int>;
  var a7: array<int, int>;
  var a8: array<int, int>;
  var a: int;
  var i: int;
  var x: int;
  assume 0 < N;
  a := 0;
  while a < N {
    tmp₁ := *;
    a1 := a1[a := tmp₁];
    tmp₂ := *;
    a7 := a7[a := tmp₂];
    a := a + 1;
  }
  i := 0;
  while i < N {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a3 := a3[i := a2[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a4 := a4[i := a3[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a5 := a5[i := a4[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a6 := a6[i := a5[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a8 := a8[i := a6[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a8 := a8[i := a7[i]];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert a1[x] == a8[x];
    x := x + 1;
  }
  result := 0;
  return;
}
