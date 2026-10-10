// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/simple_4-2_abstracted.dfy
// SV-COMP loop-acceleration/simple_4-2_abstracted.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of simple_1-1_abstracted with other constants or assertions; checks
// !(x % 2)

method main() returns (result: int) {
  var x: int;
  x := 268435440;
  if x > 0 {
    x := *;
  assume 0 <= x;
  }
  if x > 0 {
    assume false;
  }
  assert !(((rem(x, 2))) != 0);
}
