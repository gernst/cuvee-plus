// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/simple_1-1.dfy
// SV-COMP loop-acceleration/simple_1-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of simple_1-2 with other constants or assertions; checks x % 2
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

method main() returns (result: int) {
  var N: int;
  var x: int;
  assume 0 < N;
  x := 0;
  while x < N {
    x := x + 2;
  }
  assert (((rem(x, 2))) != 0);
}
