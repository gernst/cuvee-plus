// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_init1_ground-1.dfy
// SV-COMP array-examples/standard_init1_ground-1.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of standard_init1_ground-2 with other constants or assertions; checks
// a[x] == 43
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var a: array<int, int>;
  var i: int;
  var x: int;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := 42];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert a[x] == 43;
    x := x + 1;
  }
  result := 0;
  return;
}
