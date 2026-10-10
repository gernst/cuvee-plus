// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/functions_1-2.dfy
// SV-COMP loop-acceleration/functions_1-2.yml (expected: unsafe), translated from the C program
// by ./Cuvee.sh -print dfy: a variant of functions_1-1 with other constants or assertions; checks x % 2
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

method f(z: int) returns (result: int) {
  result := z + 2;
  return;
}

method main() returns (result: int) {
  var N: int;
  var x: int;
  assume 0 < N;
  x := 0;
  while x < N {
    x := f(x);
  }
  assert (((rem(x, 2))) != 0);
}
