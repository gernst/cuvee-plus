// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/brs2.dfy
// SV-COMP array-fpi/brs2.yml (expected: safe), translated from the C program by hand: a holds 2
// at the even and 0 at the odd positions, and the sum of all but a[0] is checked to be at most 2 N (brs3 to brs5
// are variants)
//
// findings: open: as ms2, the sum resets in the first iteration, i == 0, and adds the remaining elements, 2 at the
// even positions; needs the counter of the loop variable (see ifeqn1), the closed form of a trace whose first
// iteration resets it, and a bound of the sum of a remainder modulo 2 over the iterations; no lemmas tried (brs3 to
// brs5 are variants)

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  N := *;
  assume 0 < N;
  i := 0;
  while i < N {
    if i % 2 == 0 {
      a := a[i := 2];
    } else {
      a := a[i := 0];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      sum := 0;
    } else {
      sum := sum + a[i];
    }
    i := i + 1;
  }
  assert sum <= 2 * N;
}

// remaining goals of -teq -simplify:
// goal
//   forall sum₃: int, a₄: array<int, int>, N₅: int, a₁₃: array<int, int>,
//          K₁₀: Trace<int>, A₁₁: Trace<array<int, int>>, I₁₂: Trace<int>,
//          sum₂₂: int, i₂₃: int, n₁₇: int, K₁₉: Trace<int>, Sum₂₀: Trace<int>,
//          I₂₁: Trace<int> ::
//     0 < N₅ <= 536870911
//       && K₁₀ == counter(0, 1, N₅)
//       && a₁₃ == current(A₁₁)
//       && A₁₁
//         == trace(a₄, for ⌊K₁₀⌋, ⌊I₁₂⌋
//                      do a₆, k₉, i₇ ::
//                        case k₉ % 2 == 0 => a₆[k₉ := 2]
//                        case k₉ % 2 != 0 => a₆[k₉ := 0])
//       && I₁₂ == counter(0, 1, N₅)
//       && K₁₉ == counter(0, 1, n₁₇)
//       && sum₂₂ == current(Sum₂₀)
//       && i₂₃ == current(I₂₁)
//       && Sum₂₀
//         == trace(sum₃, for ⌊K₁₉⌋, ⌊I₂₁⌋
//                        do sum₁₅, k₁₈, i₁₆ ::
//                          case i₁₆ == 0 => 0 case i₁₆ != 0 => a₁₃[i₁₆] + sum₁₅)
//       && I₂₁
//         == trace(0, for ⌊K₁₉⌋
//                     do i₁₆, k₁₈ ::
//                       case i₁₆ == 0 => 1 case i₁₆ != 0 => i₁₆ + 1)
//       && invs(for ⌊K₁₉⌋, ⌊I₂₁⌋ check k₁₈, i₁₆ :: i₁₆ < N₅)
//       && 0 <= n₁₇
//       && N₅ <= i₂₃
//       ==> sum₂₂ <= 2 * N₅
