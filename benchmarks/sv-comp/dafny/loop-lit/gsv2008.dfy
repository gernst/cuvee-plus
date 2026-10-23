// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-lit/gsv2008.dfy
// SV-COMP loop-lit/gsv2008.yml (expected: safe), translated from the C program by hand: x,
// initially -50, accumulates y, which counts up from an arbitrary value above -1000, until x is nonnegative, when y
// is positive
//
// findings: x accumulates y, which counts up from an arbitrary y0, quadratic in the number of iterations; the goal
// 0 < y at the exit needs that the sum of y0, ..., y - 1 is negative if y <= 0, a nonlinear fact; no lemma is added

method main() {
  var x: int;
  var y: int;
  x := -50;
  y := *;
  while x < 0 {
    x := x + y;
    y := y + 1;
  }
  assert y > 0;
}

// remaining goals of -teq -simplify:
// goal
//   forall y₃: int, y₁₂: int, n₆: int, K₈: Trace<int>, Y₁₀: Trace<int> ::
//     0 < y₃ + 1000
//       && K₈ == counter(0, 1, n₆)
//       && y₁₂ == n₆ + y₃
//       && Y₁₀ == counter(y₃, 1, n₆)
//       && invs(for ⌊K₈⌋, ⌊Y₁₀⌋
//               check k₇, y₅ ::
//                 (y₃ + -(y₃ * y₃) + -y₅ + y₅ * y₅) / 2 < 50)
//       && y₃ <= y₁₂
//       && 50 <= (-y₁₂ + y₁₂ * y₁₂ + y₃ + -(y₃ * y₃)) / 2
//       ==> 0 < y₁₂
