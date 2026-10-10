// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/const_1-2.dfy
// SV-COMP loop-acceleration/const_1-2.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of const_1-1 with other constants or assertions; checks x == 1
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1024

method main() returns (result: int) {
  var N: int;
  var x: int;
  var y: int;
  assume 0 < N;
  x := 1;
  y := 0;
  while y < N {
    x := 0;
    y := y + 1;
  }
  assert x == 1;
}
