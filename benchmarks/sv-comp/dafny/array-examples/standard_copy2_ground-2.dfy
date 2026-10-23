// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-examples/standard_copy2_ground-2.dfy
// SV-COMP array-examples/standard_copy2_ground-2.yml (expected: safe), translated from the C program by hand:
// an arbitrary array is copied twice, and the last copy is checked to agree with it (standard_copy4 to _copy9
// are variants with more copies)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var x: int;
  var v: int;
  var a1: array<int, int>;
  var a2: array<int, int>;
  var a3: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    v := *;
    a1 := a1[i := v];
    i := i + 1;
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
  x := 0;
  while x < N {
    assert a1[x] == a3[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
