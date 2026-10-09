// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/rewrev.dfy
// SV-COMP ReachSafety-Arrays/array-tiling/rewrev.yml (expected: safe), translated from the C program by hand:
// backwards from i = S - 2 to -1, a[i] = 7 (if i >= 0) and then a[i + 1] = 3, and each element is checked to be
// at least 2
//
// findings: open: the loop runs backwards from S - 2 to -1, where the counter of -teq is mapped to the positions S
// - 2 - k, which a lemma like that of rew would have to read at decreasing positions; no lemmas tried

method main() {
  var S: int;
  var i: int;
  var a: array<int, int>;
  S := *;
  if S > 1 && S < 100000 {
    i := S - 2;
    while i >= -1 {
      if i >= 0 {
        a := a[i := 7];
      }
      a := a[i + 1 := 3];
      i := i - 1;
    }
    i := 0;
    while i < S {
      assert a[i] >= 2;
      i := i + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₃: array<int, int>, a₁₂: array<int, int>, i₁₃: int, n₇: int,
//          K₉: Trace<int>, A₁₀: Trace<array<int, int>>, I₁₁: Trace<int>, n₁₅: int,
//          K₁₇: Trace<int>, I₁₈: Trace<int> ::
//     0 <= i₁₃ + n₇ < 99998
//       && K₉ == counter(0, 1, n₇)
//       && a₁₂ == current(A₁₀)
//       && A₁₀
//         == trace(a₃, for ⌊K₉⌋, ⌊I₁₁⌋
//                      do a₅, k₈, i₆ ::
//                        case 0 <= i₆ => a₅[i₆ := 7][i₆ + 1 := 3]
//                        case i₆ < 0 => a₅[i₆ + 1 := 3])
//       && I₁₁ == counter(i₁₃ + n₇, -1, n₇)
//       && invs(for ⌊K₉⌋, ⌊I₁₁⌋ check k₈, i₆ :: 0 <= i₆ + 1)
//       && 0 <= n₇
//       && i₁₃ + 1 < 0
//       && K₁₇ == counter(0, 1, n₁₅)
//       && I₁₈ == counter(0, 1, n₁₅)
//       && invs(for ⌊K₁₇⌋, ⌊I₁₈⌋ check k₁₆, i₁₄ :: 2 <= a₁₂[k₁₆])
//       && 0 <= n₁₅ < i₁₃ + n₇ + 2
//       ==> 2 <= a₁₂[n₁₅]
