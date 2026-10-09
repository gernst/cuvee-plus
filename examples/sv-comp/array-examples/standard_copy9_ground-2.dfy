// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_copy9_ground-2.dfy
// SV-COMP array-examples/standard_copy9_ground-2.yml (expected: safe), translated from the C
// program by hand: a1 is filled with arbitrary values and copied along a chain a2, ..., a9, a0, such that a0 equals
// a1
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output), in about 20 s for the chain of
// nine copies
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var a0: array<int, int>;
  var a1: array<int, int>;
  var a2: array<int, int>;
  var a3: array<int, int>;
  var a4: array<int, int>;
  var a5: array<int, int>;
  var a6: array<int, int>;
  var a7: array<int, int>;
  var a8: array<int, int>;
  var a9: array<int, int>;
  var a: int;
  var i: int;
  var x: int;
  var tmp: int;
  assume 0 < N;
  a := 0;
  while a < N {
    tmp := *;
    a1 := a1[a := tmp];
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
    a7 := a7[i := a6[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a8 := a8[i := a7[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a9 := a9[i := a8[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a0 := a0[i := a9[i]];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert a1[x] == a0[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
