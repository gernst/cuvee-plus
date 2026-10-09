// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/nr2.dfy
// SV-COMP ReachSafety-Arrays/array-tiling/nr2.yml (expected: safe), translated from the C program by hand:
// as pr2, with MINVAL = 2, where an inner loop j = 2, 1 stores j or 0 at 2 i - j
//
// findings: open: the inner loop j = 2, 1 is a nested loop, whose two iterations -teq summarizes by iteration
// constraints over sequences of traces (see array-multidimensional/init-2-n-u.dfy); no lemmas tried (nr3 to nr5 are
// variants)

method main() {
  var C: int;
  var i: int;
  var j: int;
  var MINVAL: int;
  var a: array<int, int>;
  C := *;
  if C > 1 {
    MINVAL := 2;
    if C % 2 != 0 {
      return;
    }
    i := 1;
    while i <= C / 2 {
      j := 2;
      while j >= 1 {
        if j >= MINVAL {
          a := a[i * 2 - j := j];
        } else {
          a := a[i * 2 - j := 0];
        }
        j := j - 1;
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
//   forall a₅: array<int, int>, C₆: int, a₃₂: array<int, int>, n₂₅: int,
//          K₂₇: Trace<int>, A₂₉: Trace<array<int, int>>, I₃₀: Trace<int>,
//          A?₁₉: seq<array<int, int>>, J?₂₀: seq<int>, N?₂₁: seq<int>,
//          K?₂₂: seq<Trace<int>>, A?₂₃: seq<Trace<array<int, int>>>,
//          J?₂₄: seq<Trace<int>>, n₄₄: int, K₄₆: Trace<int>, I₄₇: Trace<int> ::
//     1 < C₆
//       && C₆ % 2 == 0
//       && K₂₇ == counter(0, 1, n₂₅)
//       && a₃₂ == current(A₂₉)
//       && A₂₉ == trace(a₅, for ⌊K₂₇⌋, A?₁₉ do a₈, k₂₆, a₁₇ :: a₁₇)
//       && I₃₀ == counter(1, 1, n₂₅)
//       && (n₂₅ == 0 || 0 < C₆ / 2 && n₂₅ == C₆ / 2)
//       && invs(for ⌊K₂₇⌋, ⌊I₃₀⌋, N?₂₁, K?₂₂
//               check k₂₆, i₉, n₁₂, K₁₄ ::
//                 K₁₄ == counter(0, 1, n₁₂))
//       && invs(for ⌊K₂₇⌋, ⌊I₃₀⌋, A?₁₉, A?₂₃
//               check k₂₆, i₉, a₁₇, A₁₅ ::
//                 a₁₇ == current(A₁₅))
//       && invs(for ⌊K₂₇⌋, ⌊I₃₀⌋, J?₂₀, J?₂₄
//               check k₂₆, i₉, j₁₈, J₁₆ ::
//                 j₁₈ == current(J₁₆))
//       && invs(for ⌊K₂₇⌋, ⌊A₂₉⌋, ⌊I₃₀⌋, A?₂₃, J?₂₄
//               check k₂₆, a₈, i₉, A₁₅, J₁₆ ::
//                 A₁₅
//                   == trace(a₈, for ⌊J₁₆⌋
//                                do a₁₀, j₁₁ ::
//                                  case 2 <= j₁₁ => a₁₀[-j₁₁ + 2 * k₂₆ + 2 := j₁₁]
//                                  case j₁₁ < 2 => a₁₀[-j₁₁ + 2 * k₂₆ + 2 := 0]))
//       && invs(for ⌊K₂₇⌋, ⌊I₃₀⌋, K?₂₂, J?₂₄
//               check k₂₆, i₉, K₁₄, J₁₆ ::
//                 J₁₆ == sums(2, maps(for ⌊K₁₄⌋ yield k₁₃ :: -1)))
//       && invs(for ⌊K₂₇⌋, ⌊I₃₀⌋, J?₂₄
//               check k₂₆, i₉, J₁₆ ::
//                 invs(for ⌊J₁₆⌋ check j₁₁ :: 1 <= j₁₁))
//       && invs(for ⌊K₂₇⌋, ⌊I₃₀⌋, N?₂₁ check k₂₆, i₉, n₁₂ :: 0 <= n₁₂)
//       && invs(for ⌊K₂₇⌋, ⌊I₃₀⌋, J?₂₀ check k₂₆, i₉, j₁₈ :: j₁₈ < 1)
//       && 0 <= n₂₅
//       && C₆ / 2 <= n₂₅
//       && K₄₆ == counter(0, 1, n₄₄)
//       && I₄₇ == counter(0, 1, n₄₄)
//       && invs(for ⌊K₄₆⌋, ⌊I₄₇⌋ check k₄₅, i₄₃ :: 2 <= a₃₂[k₄₅] || a₃₂[k₄₅] == 0)
//       && 0 <= n₄₄ < C₆
//       ==> 2 <= a₃₂[n₄₄] || a₃₂[n₄₄] == 0
