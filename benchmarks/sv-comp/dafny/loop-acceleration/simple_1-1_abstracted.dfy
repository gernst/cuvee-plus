// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/simple_1-1_abstracted.dfy
// SV-COMP loop-acceleration/simple_1-1_abstracted.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a program of the folder; checks x % 2

method main() returns (result: int) {
  var x: int;
  var x__VERIFIER_LA_tmp0: int;
  var __VERIFIER_LA_iterations0: int;
  var x__VERIFIER_LA_old_tmp0: int;
  x := 0;
  if x < 268435455 {
    x__VERIFIER_LA_tmp0 := x;
    __VERIFIER_LA_iterations0 := (quot(268435455 - x__VERIFIER_LA_tmp0, 2));
    x__VERIFIER_LA_old_tmp0 := x;
    x := __VERIFIER_LA_iterations0 * 2 + x__VERIFIER_LA_old_tmp0;
  }
  assert (((rem(x, 2))) != 0);
}
