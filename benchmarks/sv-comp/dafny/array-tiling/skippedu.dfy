// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-tiling/skippedu.dfy
// SV-COMP array-tiling/skippedu.yml (expected: unsafe), translated from the C program by hand:
// as skipped, but the elements are clamped to i instead of their position, which is below the positions 2 i - 1
// for i > 1
//
// findings: unsafe: the values are clamped to i instead of their positions, which is below the position 2 i - 1 for
// i > 1; open, as expected

method main() {
  var S: int;
  var i: int;
  var v: int;
  var a: array<int, int>;
  S := *;
  if S > 1 && S < 100000 {
    i := 0;
    while i < S {
      v := *;
      a := a[i := v];
      i := i + 1;
    }
    if S % 2 != 0 {
      return;
    }
    i := 1;
    while i <= S / 2 {
      if a[2 * i - 2] > i {
        a := a[2 * i - 2 := i];
      }
      if a[2 * i - 1] > i {
        a := a[2 * i - 1 := i];
      }
      i := i + 1;
    }
    i := 0;
    while i < S {
      assert a[i] <= i;
      i := i + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₄: array<int, int>, S₅: int, a₁₈: array<int, int>,
//          A₁₅: Trace<array<int, int>>, I₁₆: Trace<int>, V?₁₀: seq<int>,
//          a₂₈: array<int, int>, n₂₃: int, K₂₅: Trace<int>,
//          A₂₆: Trace<array<int, int>>, I₂₇: Trace<int>, n₃₁: int,
//          K₃₃: Trace<int>, I₃₄: Trace<int> ::
//     1 < S₅ < 100000
//       && a₁₈ == current(A₁₅)
//       && A₁₅ == stores(a₄, ⌊I₁₆⌋, V?₁₀)
//       && I₁₆ == counter(0, 1, S₅)
//       && S₅ % 2 == 0
//       && K₂₅ == counter(0, 1, n₂₃)
//       && a₂₈ == current(A₂₆)
//       && A₂₆
//         == trace(a₁₈, for ⌊K₂₅⌋, ⌊I₂₇⌋
//                       do a₂₁, k₂₄, i₂₂ ::
//                         case k₂₄ + 1 < a₂₁[2 * k₂₄]
//                           && k₂₄ + 1 < a₂₁[2 * k₂₄ := i₂₂][2 * k₂₄ + 1] => a₂₁[
//                           2 * k₂₄ :=
//                           i₂₂][
//                           2 * k₂₄ + 1 :=
//                           i₂₂]
//                         case k₂₄ + 1 < a₂₁[2 * k₂₄]
//                           && a₂₁[2 * k₂₄ := i₂₂][2 * k₂₄ + 1] <= k₂₄ + 1 => a₂₁[
//                           2 * k₂₄ :=
//                           i₂₂]
//                         case a₂₁[2 * k₂₄] <= k₂₄ + 1 < a₂₁[2 * k₂₄ + 1] => a₂₁[
//                           2 * k₂₄ + 1 :=
//                           i₂₂]
//                         case a₂₁[2 * k₂₄] <= k₂₄ + 1
//                           && a₂₁[2 * k₂₄ + 1] <= k₂₄ + 1 => a₂₁)
//       && I₂₇ == counter(1, 1, n₂₃)
//       && (n₂₃ == 0 || 0 < S₅ / 2 && n₂₃ == S₅ / 2)
//       && invs(for ⌊K₂₅⌋, ⌊A₂₆⌋, ⌊I₂₇⌋
//               check k₂₄, a₂₁, i₂₂ ::
//                 k₂₄ + 1 < a₂₁[2 * k₂₄]
//                   && k₂₄ + 1 < a₂₁[2 * k₂₄ := i₂₂][2 * k₂₄ + 1]
//                   || k₂₄ + 1 < a₂₁[2 * k₂₄]
//                     && a₂₁[2 * k₂₄ := i₂₂][2 * k₂₄ + 1] <= k₂₄ + 1
//                   || a₂₁[2 * k₂₄] <= k₂₄ + 1 < a₂₁[2 * k₂₄ + 1]
//                   || a₂₁[2 * k₂₄] <= k₂₄ + 1 && a₂₁[2 * k₂₄ + 1] <= k₂₄ + 1)
//       && 0 <= n₂₃
//       && S₅ / 2 <= n₂₃
//       && K₃₃ == counter(0, 1, n₃₁)
//       && I₃₄ == counter(0, 1, n₃₁)
//       && invs(for ⌊K₃₃⌋, ⌊I₃₄⌋ check k₃₂, i₃₀ :: a₂₈[k₃₂] <= k₃₂)
//       && 0 <= n₃₁ < S₅
//       ==> a₂₈[n₃₁] <= n₃₁
