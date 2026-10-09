// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/in-de31.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/in-de31.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x counts down from n while y counts up, then y is moved back through z, and z == n is
// checked
//
// findings: open: the three loops move the value n from x to y to z and back, which -teq summarizes by counters,
// and the goal remains as facts over several variables with disjunctions of the exits, which are no difference
// constraints and are not split (see TODO.md); no lemmas tried (in-de32 to in-de62 are variants)

method main() returns (result: int) {
  var tmp₁: int;
  {
    var n: int, x: int, y: int, z: int;
    tmp₁ := *;
    assume 0 <= tmp₁;
    n := tmp₁;
    x := n;
    y := 0;
    while x > 0 {
      x := x - 1;
      y := y + 1;
    }
    z := y;
    while z > 0 {
      x := x + 1;
      z := z - 1;
    }
    while y > 0 {
      y := y - 1;
      z := z + 1;
    }
    assert z == n;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall x₁₄: int, z₂₄: int, y₃₂: int, z₃₃: int ::
//     z₂₄ <= x₁₄ + y₃₂ + z₃₃
//       && (y₃₂ + z₃₃ == z₂₄ || z₂₄ < y₃₂ + z₃₃ && 0 == x₁₄)
//       && z₂₄ <= y₃₂ + z₃₃
//       && x₁₄ <= 0
//       && (y₃₂ + z₃₃ == 2 * z₂₄ || 1 <= y₃₂ + z₃₃ && 0 == z₂₄)
//       && z₂₄ <= 0
//       && (z₃₃ == z₂₄ || z₂₄ < z₃₃ && 0 == y₃₂)
//       && z₂₄ <= z₃₃
//       && y₃₂ <= 0
//       ==> z₂₄ == x₁₄ + y₃₂
