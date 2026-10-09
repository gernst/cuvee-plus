// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/ms2.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/ms2.yml (expected: safe), translated from the C program by hand: a[i] = i %
// 2, and the sum of all but a[0] is checked to be at most N (ms3 to ms5 are variants)
//
// findings: open: the sum resets at i == 0 and then adds i % 2; as brs2, it needs the counter of the loop variable,
// the closed form of a trace whose first iteration resets it, a bound of the sum of remainders, and the number of
// iterations n <= N, which is the iteration constraint i < N only; no lemmas tried (ms3 to ms5 are variants)

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  havoc N;
  assume 0 < N <= 536870911;
  i := 0;
  while i < N {
    a := a[i := i % 2];
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
  assert sum <= N;
}

// remaining goals of -teq -simplify:
// goal
//   forall sum₃: int, a₄: array<int, int>, N₅: int, sum₂₂: int, i₂₃: int,
//          n₁₇: int, K₁₉: Trace<int>, Sum₂₀: Trace<int>, I₂₁: Trace<int> ::
//     0 < N₅ <= 536870911
//       && K₁₉ == counter(0, 1, n₁₇)
//       && sum₂₂ == current(Sum₂₀)
//       && i₂₃ == current(I₂₁)
//       && Sum₂₀
//         == trace(sum₃, for ⌊K₁₉⌋, ⌊I₂₁⌋
//                        do sum₁₅, k₁₈, i₁₆ ::
//                          case i₁₆ == 0 => 0
//                          case i₁₆ != 0 => (if 0 < i₁₆ then i₁₆ % 2 else a₄[i₁₆])
//                            + sum₁₅)
//       && I₂₁
//         == trace(0, for ⌊K₁₉⌋
//                     do i₁₆, k₁₈ ::
//                       case i₁₆ == 0 => 1 case i₁₆ != 0 => i₁₆ + 1)
//       && invs(for ⌊K₁₉⌋, ⌊I₂₁⌋ check k₁₈, i₁₆ :: i₁₆ < N₅)
//       && 0 <= n₁₇
//       && N₅ <= i₂₃
//       ==> sum₂₂ <= N₅
