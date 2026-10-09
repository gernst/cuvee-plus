// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/simple_1-1_abstracted.dfy
// SV-COMP loop-acceleration/simple_1-1_abstracted.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a program of the folder; checks x % 2

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  {
    var x: int;
    x := 0;
    if x < 268435455 {
      var x__VERIFIER_LA_tmp0: int;
      var __VERIFIER_LA_iterations0: int;
      var x__VERIFIER_LA_old_tmp0: int;
      x__VERIFIER_LA_tmp0 := x;
      __VERIFIER_LA_iterations0 := (quotient(268435455 - x__VERIFIER_LA_tmp0, 2));
      x__VERIFIER_LA_old_tmp0 := x;
      x := __VERIFIER_LA_iterations0 * 2 + x__VERIFIER_LA_old_tmp0;
    }
    assert (((remainder(x, 2))) != 0);
  }
}
