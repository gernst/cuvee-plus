// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-zilu/benchmark52_polynomial.dfy
// SV-COMP ReachSafety-Loops/loop-zilu/benchmark52_polynomial.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: i counts up while i * i < 100, and i == 10 is checked
//
// findings: open: the loop test i * i < 100 is non-linear; the goal needs that the first i from i0 with i * i >=
// 100 is 10, from the iteration constraint at the last iteration, which teq.dfy does not decide for polynomials

method main() returns (result: int) {
  var tmp₁: int;
  {
    var i: int;
    havoc tmp₁;
    i := tmp₁;
    if !(i < 10 && i > -10) {
      result := 0;
      return;
    }
    while i * i < 100 {
      i := i + 1;
    }
    assert i == 10;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall tmp₃: int, n₅: int, K₇: Trace<int>, I₈: Trace<int> ::
//     tmp₃ < 10
//       && 0 < tmp₃ + 10
//       && K₇ == counter(0, 1, n₅)
//       && I₈ == counter(tmp₃, 1, n₅)
//       && invs(for ⌊K₇⌋, ⌊I₈⌋
//               check k₆, i₄ ::
//                 2 * k₆ * tmp₃ + k₆ * k₆ + tmp₃ * tmp₃ < 100)
//       && 0 <= n₅
//       && 100 <= 2 * n₅ * tmp₃ + n₅ * n₅ + tmp₃ * tmp₃
//       ==> n₅ + tmp₃ == 10
