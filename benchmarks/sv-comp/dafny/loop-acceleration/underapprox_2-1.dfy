// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-acceleration/underapprox_2-1.dfy
// SV-COMP loop-acceleration/underapprox_2-1.yml (expected: unsafe), translated from the C program
// by ./Cuvee.sh -print dfy: a variant of underapprox_1-1 with other constants or assertions; checks x != 6
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 6

method main() returns (result: int) {
  var N: int;
  var x: int;
  var y: int;
  assume 0 < N;
  x := 0;
  y := 1;
  while x < N {
    x := x + 1;
    y := y * 2;
  }
  assert x != N;
}
