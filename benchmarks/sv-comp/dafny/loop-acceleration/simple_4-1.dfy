// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/simple_4-1.dfy
// SV-COMP loop-acceleration/simple_4-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of simple_1-1 with other constants or assertions; checks !(x % 2)

method main() returns (result: int) {
  var x: int;
  x := 268435441;
  while x > 1 {
    x := x - 2;
  }
  assert !(((rem(x, 2))) != 0);
}
