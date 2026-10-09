// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark43_conjunctive.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark43_conjunctive.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: x and y count up together while both are below 100, and one of them reaches 100
//
// findings: open: the goal needs the fact tmp + x < y + 100 over three variables, which is no difference
// constraint, combined with the cases of the exit (see seq-3, TODO.md) (benchmark43_conjunctive_abstracted is a
// variant)

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int;
  {
    var x: int, y: int;
    havoc tmp₁;
    x := tmp₁;
    havoc tmp₂;
    y := tmp₂;
    if !(x < 100 && y < 100) {
      result := 0;
      return;
    }
    while x < 100 && y < 100 {
      x := x + 1;
      y := y + 1;
    }
    assert x == 100 || y == 100;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall tmp₆: int, x₁₄: int, y₁₅: int ::
//     tmp₆ + x₁₄ < y₁₅ + 100
//       && tmp₆ < 100
//       && (y₁₅ == tmp₆ || x₁₄ < 101 && y₁₅ < 101)
//       && tmp₆ <= y₁₅
//       ==> x₁₄ < 100 && y₁₅ < 100 || x₁₄ == 100 || y₁₅ == 100
