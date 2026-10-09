// ./Cuvee.sh -teq -simplify examples/sv-comp/array-industry-pattern/array_assert_loop_dep.dfy
// SV-COMP ReachSafety-Arrays/array-industry-pattern/array_assert_loop_dep.yml (expected: unsafe), translated from the C program by hand:
// the array is set to 10, and the second loop checks a[i] == 10 before it sets a[i + 1] to 20, except at 15000,
// such that a[1] is 20 when checked
//
// findings: unsafe: a[1] is 20 when it is checked, set by the iteration before; open, as expected, -teq records the
// check as an iteration constraint over the array at each iteration
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := 10];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == 10;
    if i + 1 != 15000 {
      a := a[i + 1 := 20];
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₂: array<int, int>, a₁₀: array<int, int>, A₈: Trace<array<int, int>>,
//          I₉: Trace<int>, a₁₉: array<int, int>, i₂₀: int, n₁₄: int,
//          K₁₆: Trace<int>, A₁₇: Trace<array<int, int>>, I₁₈: Trace<int> ::
//     a₁₀ == current(A₈)
//       && A₈ == stores(a₂, ⌊I₉⌋, ⌊consts(100000, 10)⌋)
//       && I₉ == counter(0, 1, 100000)
//       && K₁₆ == counter(0, 1, n₁₄)
//       && a₁₉ == current(A₁₇)
//       && i₂₀ == current(I₁₈)
//       && A₁₇
//         == trace(a₁₀, for ⌊K₁₆⌋, ⌊I₁₈⌋
//                       do a₁₂, k₁₅, i₁₃ ::
//                         case i₁₃ != 14999 => a₁₂[i₁₃ + 1 := 20]
//                         case i₁₃ == 14999 => a₁₂)
//       && I₁₈
//         == trace(0, for ⌊K₁₆⌋
//                     do i₁₃, k₁₅ ::
//                       case i₁₃ != 14999 => i₁₃ + 1 case i₁₃ == 14999 => 15000)
//       && invs(for ⌊K₁₆⌋, ⌊I₁₈⌋ check k₁₅, i₁₃ :: i₁₃ < 100000)
//       && invs(for ⌊K₁₆⌋, ⌊A₁₇⌋, ⌊I₁₈⌋
//               check k₁₅, a₁₂, i₁₃ ::
//                 i₁₃ != 14999 && a₁₂[i₁₃] == 10
//                   || i₁₃ == 14999 && a₁₂[14999] == 10)
//       && 0 <= n₁₄
//       && i₂₀ < 100000
//       ==> a₁₉[i₂₀] == 10
