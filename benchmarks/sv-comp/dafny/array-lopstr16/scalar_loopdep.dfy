// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-lopstr16/scalar_loopdep.dfy
// SV-COMP array-lopstr16/scalar_loopdep.yml (expected: safe), translated from the C program by hand:
// a[i] = y, where y counts up from 100, and a[i] >= 100 is checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var x: int;
  var y: int;
  var a: array<int, int>;
  assume 0 < N;
  y := 100;
  i := 0;
  while i < N {
    x := y;
    a := a[i := y];
    y := y + 1;
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] >= 100;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
