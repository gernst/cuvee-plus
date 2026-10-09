// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/trex03-2.dfy
// SV-COMP loops/trex03-2.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: one of three counters x1, x2, x3 is decremented by 1 in each iteration, chosen nondeterministically, while
// all are positive, and one of them is checked to be 0 at the end (unsigned int is int)
//
// findings: open: one of three counters is decremented in each iteration, chosen by nondeterministic flags; the
// exit needs that the test of the last iteration, all positive, and one decrement give a zero, i.e., the case of
// the last iteration; no lemmas tried

method main() returns (result: int) {
  var tmp₁: int, tmp₂: int, tmp₃: int, tmp₄: bool, tmp₅: bool;
  {
    var
      x1: int,
      x2: int,
      x3: int,
      d1: int,
      d2: int,
      d3: int,
      c1: bool,
      c2: bool;
    tmp₁ := *;
    assume 0 <= tmp₁;
    x1 := tmp₁;
    tmp₂ := *;
    assume 0 <= tmp₂;
    x2 := tmp₂;
    tmp₃ := *;
    assume 0 <= tmp₃;
    x3 := tmp₃;
    d1 := 1;
    d2 := 1;
    d3 := 1;
    tmp₄ := *;
    c1 := tmp₄;
    tmp₅ := *;
    c2 := tmp₅;
    while x1 > 0 && x2 > 0 && x3 > 0 {
      if c1 {
        x1 := x1 - d1;
      } else if c2 {
        x2 := x2 - d2;
      } else {
        x3 := x3 - d3;
      }
      c1 := *;
      c2 := *;
    }
    assert x1 == 0 || x2 == 0 || x3 == 0;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall tmp₁₄: int, tmp₁₅: int, tmp₁₆: int, tmp₁₇: bool, tmp₁₈: bool,
//          x2₄₄: int, x1₄₅: int, x3₄₇: int, n₃₆: int, K₃₈: Trace<int>,
//          X2₃₉: Trace<int>, X1₄₀: Trace<int>, C2₄₁: Trace<bool>,
//          X3₄₂: Trace<int>, C1₄₃: Trace<bool>, C1?₃₀: seq<bool>,
//          C2?₃₁: seq<bool>, C1?₃₂: seq<bool>, C2?₃₃: seq<bool>, C1?₃₄: seq<bool>,
//          C2?₃₅: seq<bool> ::
//     0 <= tmp₁₄
//       && 0 <= tmp₁₅
//       && 0 <= tmp₁₆
//       && K₃₈ == counter(0, 1, n₃₆)
//       && x2₄₄ == current(X2₃₉)
//       && x1₄₅ == current(X1₄₀)
//       && x3₄₇ == current(X3₄₂)
//       && X2₃₉
//         == trace(tmp₁₅, for ⌊K₃₈⌋, ⌊C2₄₁⌋, ⌊C1₄₃⌋
//                         do x2₁₉, k₃₇, c2₂₁, c1₂₃ ::
//                           case c1₂₃ || !c2₂₁ => x2₁₉
//                           case !c1₂₃ && c2₂₁ => x2₁₉ + -1)
//       && X1₄₀
//         == trace(tmp₁₄, for ⌊K₃₈⌋, ⌊C1₄₃⌋
//                         do x1₂₀, k₃₇, c1₂₃ ::
//                           case c1₂₃ => x1₂₀ + -1 case !c1₂₃ => x1₂₀)
//       && C2₄₁
//         == trace(tmp₁₈, for ⌊K₃₈⌋, ⌊C1₄₃⌋, C2?₃₁, C2?₃₃, C2?₃₅
//                         do c2₂₁, k₃₇, c1₂₃, c2₂₇, c2₂₈, c2₂₉ ::
//                           case c1₂₃ => c2₂₇
//                           case !c1₂₃ && c2₂₁ => c2₂₈
//                           case !c1₂₃ && !c2₂₁ => c2₂₉)
//       && X3₄₂
//         == trace(tmp₁₆, for ⌊K₃₈⌋, ⌊C2₄₁⌋, ⌊C1₄₃⌋
//                         do x3₂₂, k₃₇, c2₂₁, c1₂₃ ::
//                           case c1₂₃ || c2₂₁ => x3₂₂
//                           case !c1₂₃ && !c2₂₁ => x3₂₂ + -1)
//       && C1₄₃
//         == trace(tmp₁₇, for ⌊K₃₈⌋, ⌊C2₄₁⌋, C1?₃₀, C1?₃₂, C1?₃₄
//                         do c1₂₃, k₃₇, c2₂₁, c1₂₄, c1₂₅, c1₂₆ ::
//                           case c1₂₃ => c1₂₄
//                           case !c1₂₃ && c2₂₁ => c1₂₅
//                           case !c1₂₃ && !c2₂₁ => c1₂₆)
//       && invs(for ⌊K₃₈⌋, ⌊X1₄₀⌋ check k₃₇, x1₂₀ :: 0 < x1₂₀)
//       && invs(for ⌊K₃₈⌋, ⌊X2₃₉⌋ check k₃₇, x2₁₉ :: 0 < x2₁₉)
//       && invs(for ⌊K₃₈⌋, ⌊X3₄₂⌋ check k₃₇, x3₂₂ :: 0 < x3₂₂)
//       && 0 <= n₃₆
//       ==> 0 < x1₄₅ && 0 < x2₄₄ && 0 < x3₄₇
//         || x1₄₅ == 0
//         || x2₄₄ == 0
//         || x3₄₇ == 0
