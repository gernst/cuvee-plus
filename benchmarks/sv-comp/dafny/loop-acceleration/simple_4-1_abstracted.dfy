// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-acceleration/simple_4-1_abstracted.dfy
// SV-COMP loop-acceleration/simple_4-1_abstracted.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of simple_1-1_abstracted with other constants or assertions; checks
// !(x % 2)

method main() returns (result: int) {
  var x: int;
  var x__VERIFIER_LA_tmp0: int;
  var __VERIFIER_LA_iterations0: int;
  var x__VERIFIER_LA_old_tmp0: int;
  x := 268435441;
  if x > 1 {
    x__VERIFIER_LA_tmp0 := x;
    __VERIFIER_LA_iterations0 := (quot(x__VERIFIER_LA_tmp0 - 1, 2)) + 1;
    x__VERIFIER_LA_old_tmp0 := x;
    x := __VERIFIER_LA_iterations0 * -2 + x__VERIFIER_LA_old_tmp0;
  }
  assert !(((rem(x, 2))) != 0);
}
