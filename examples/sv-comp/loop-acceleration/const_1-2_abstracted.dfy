// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/const_1-2_abstracted.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/const_1-2_abstracted.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a program of the folder; checks x == 1

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

method main() returns (result: int) {
  {
    var x: int;
    var y: int;
    x := 1;
    y := 0;
    if y < 1024 {
      var y__VERIFIER_LA_tmp0: int;
      var __VERIFIER_LA_iterations0: int;
      var x__VERIFIER_LA_old_tmp0: int;
      var y__VERIFIER_LA_old_tmp0: int;
      y__VERIFIER_LA_tmp0 := y;
      __VERIFIER_LA_iterations0 := (quotient(1024 - y__VERIFIER_LA_tmp0, 1));
      x__VERIFIER_LA_old_tmp0 := x;
      x := __VERIFIER_LA_iterations0 * 0 + x__VERIFIER_LA_old_tmp0 * 0 + 0;
      y__VERIFIER_LA_old_tmp0 := y;
      y := __VERIFIER_LA_iterations0 * 1 + y__VERIFIER_LA_old_tmp0;
    }
    assert x == 1;
  }
}
