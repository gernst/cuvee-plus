// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/standard_init2_ground-2.dfy
// SV-COMP array-examples/standard_init2_ground-2.yml (expected: safe), translated from the C program by hand:
// the array is set to 42 and then to 43, which is checked (standard_init3 to _init9 are variants with more
// loops)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var x: int;
  var a: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := 43];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert a[x] == 43;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
