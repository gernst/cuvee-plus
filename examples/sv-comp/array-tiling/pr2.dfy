// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/pr2.dfy
// SV-COMP ReachSafety-Arrays/array-tiling/pr2.yml (expected: safe), translated from the C program by hand:
// as mbpr2, but both positions in one loop, and MINVAL is not initialized (arbitrary)
//
// findings: MINVAL is arbitrary, hence the tests of the stores at 2 k and 2 k + 1 are the same in all iterations,
// which -teq turns into three cases of the update over MINVAL; open: the closed form of stores at 2 k and 2 k + 1
// (see array-cav19/array_doub_access_init_const.dfy) applies to each case, but the cases whose guards do not depend
// on the iteration are not split into separate traces, nor joined into conditional values (see the summary, scalar
// updates whose condition is the same in all iterations); no lemmas tried (pr3 to pr5 are variants)

method main() {
  var C: int;
  var i: int;
  var MINVAL: int;
  var V2: int;
  var V1: int;
  var a: array<int, int>;
  havoc C;
  if C > 1 {
    havoc MINVAL;
    V2 := 3;
    V1 := 1;
    if C % 2 != 0 {
      return;
    }
    i := 1;
    while i <= C / 2 {
      if V2 >= MINVAL {
        a := a[i * 2 - 2 := V2];
      } else {
        a := a[i * 2 - 2 := 0];
      }
      if V1 >= MINVAL {
        a := a[i * 2 - 1 := V1];
      } else {
        a := a[i * 2 - 1 := 0];
      }
      i := i + 1;
    }
    i := 0;
    while i < C {
      assert a[i] >= MINVAL || a[i] == 0;
      i := i + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₆: array<int, int>, C₇: int, MINVAL₈: int, a₁₆: array<int, int>,
//          n₁₁: int, K₁₃: Trace<int>, A₁₄: Trace<array<int, int>>,
//          I₁₅: Trace<int>, n₁₉: int, K₂₁: Trace<int>, I₂₂: Trace<int> ::
//     1 < C₇
//       && C₇ % 2 == 0
//       && K₁₃ == counter(0, 1, n₁₁)
//       && a₁₆ == current(A₁₄)
//       && A₁₄
//         == trace(a₆, for ⌊K₁₃⌋, ⌊I₁₅⌋
//                      do a₉, k₁₂, i₁₀ ::
//                        case MINVAL₈ <= 1 => a₉[2 * k₁₂ := 3][2 * k₁₂ + 1 := 1]
//                        case MINVAL₈ <= 3 && 1 < MINVAL₈ => a₉[2 * k₁₂ := 3][
//                          2 * k₁₂ + 1 :=
//                          0]
//                        case 3 < MINVAL₈ => a₉[2 * k₁₂ := 0][2 * k₁₂ + 1 := 0])
//       && I₁₅ == counter(1, 1, n₁₁)
//       && (n₁₁ == 0 || 0 < C₇ / 2 && n₁₁ == C₇ / 2)
//       && 0 <= n₁₁
//       && C₇ / 2 <= n₁₁
//       && K₂₁ == counter(0, 1, n₁₉)
//       && I₂₂ == counter(0, 1, n₁₉)
//       && invs(for ⌊K₂₁⌋, ⌊I₂₂⌋
//               check k₂₀, i₁₈ ::
//                 MINVAL₈ <= a₁₆[k₂₀] || a₁₆[k₂₀] == 0)
//       && 0 <= n₁₉ < C₇
//       ==> MINVAL₈ <= a₁₆[n₁₉] || a₁₆[n₁₉] == 0
