// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/standard_copyInitSum2_ground-1.dfy
// SV-COMP array-examples/standard_copyInitSum2_ground-1.yml (expected: unsafe), translated from
// the C program by ./Cuvee.sh -print dfy: a variant of standard_copyInitSum2_ground-2 with other constants or
// assertions; checks b[x] == 42 + x
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var x: int;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := b[i] + i];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert b[x] == 42 + x;
    x := x + 1;
  }
  result := 0;
  return;
}
