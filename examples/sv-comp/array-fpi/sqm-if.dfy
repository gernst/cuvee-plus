// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/sqm-if.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/sqm-if.yml (expected: safe), translated from the C program by hand: as
// nsqm-if from 1 instead of N + 1, checked to be (i + 1) * (i + 1)
//
// findings: open: as nsqm-if from 1; the variant without the case is sqm

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  havoc N;
  assume 0 < N <= 536870911;
  i := 0;
  while i < N {
    if i == 0 {
      b := b[0 := 1];
    } else {
      b := b[i := b[i - 1] + 2];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      a := a[0 := 1];
    } else {
      a := a[i := a[i - 1] + b[i - 1] + 2];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == (i + 1) * (i + 1);
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₃: array<int, int>, b₄: array<int, int>, N₅: int,
//          b₁₃: array<int, int>, i₁₄: int, n₈: int, K₁₀: Trace<int>,
//          B₁₁: Trace<array<int, int>>, I₁₂: Trace<int>, a₂₂: array<int, int>,
//          i₂₃: int, n₁₇: int, K₁₉: Trace<int>, A₂₀: Trace<array<int, int>>,
//          I₂₁: Trace<int>, n₂₅: int, K₂₇: Trace<int>, I₂₈: Trace<int> ::
//     N₅ <= 536870911
//       && K₁₀ == counter(0, 1, n₈)
//       && b₁₃ == current(B₁₁)
//       && i₁₄ == current(I₁₂)
//       && B₁₁
//         == trace(b₄, for ⌊K₁₀⌋, ⌊I₁₂⌋
//                      do b₆, k₉, i₇ ::
//                        case i₇ == 0 => b₆[0 := 1]
//                        case i₇ != 0 => b₆[i₇ := b₆[i₇ + -1] + 2])
//       && I₁₂
//         == trace(0, for ⌊K₁₀⌋
//                     do i₇, k₉ ::
//                       case i₇ == 0 => 1 case i₇ != 0 => i₇ + 1)
//       && invs(for ⌊K₁₀⌋, ⌊I₁₂⌋ check k₉, i₇ :: i₇ < N₅)
//       && 0 <= n₈
//       && N₅ <= i₁₄
//       && K₁₉ == counter(0, 1, n₁₇)
//       && a₂₂ == current(A₂₀)
//       && i₂₃ == current(I₂₁)
//       && A₂₀
//         == trace(a₃, for ⌊K₁₉⌋, ⌊I₂₁⌋
//                      do a₁₅, k₁₈, i₁₆ ::
//                        case i₁₆ == 0 => a₁₅[0 := 1]
//                        case i₁₆ != 0 => a₁₅[
//                          i₁₆ :=
//                          a₁₅[i₁₆ + -1] + b₁₃[i₁₆ + -1] + 2])
//       && I₂₁
//         == trace(0, for ⌊K₁₉⌋
//                     do i₁₆, k₁₈ ::
//                       case i₁₆ == 0 => 1 case i₁₆ != 0 => i₁₆ + 1)
//       && invs(for ⌊K₁₉⌋, ⌊I₂₁⌋ check k₁₈, i₁₆ :: i₁₆ < N₅)
//       && 0 <= n₁₇
//       && N₅ <= i₂₃
//       && K₂₇ == counter(0, 1, n₂₅)
//       && I₂₈ == counter(0, 1, n₂₅)
//       && invs(for ⌊K₂₇⌋, ⌊I₂₈⌋
//               check k₂₆, i₂₄ ::
//                 a₂₂[k₂₆] == 2 * k₂₆ + k₂₆ * k₂₆ + 1)
//       && 0 <= n₂₅ < N₅
//       ==> a₂₂[n₂₅] == 2 * n₂₅ + n₂₅ * n₂₅ + 1
