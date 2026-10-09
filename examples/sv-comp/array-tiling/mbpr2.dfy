// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/mbpr2.dfy
// SV-COMP ReachSafety-Arrays/array-tiling/mbpr2.yml (expected: safe), translated from the C program by hand:
// an array of even length 2 m gets 3 or 0 (by a test that holds) at the even positions 2 i - 2 and keeps the
// odd ones in a first loop, and 1 or 0 (by a test that fails) at the odd positions 2 i - 1 in a second loop;
// each element is checked to be at least MINVAL = 2 or 0
//
// findings: the stores at 2 i - 2 and 2 i - 1 are guarded by tests on constants, which -teq decides, but the first
// loop also stores a[2 i - 1] back into itself, and the second a[2 i - 2]; open: the reads need the closed forms of
// stores at 2 k and 2 k + 1 in two loops, one of them a store of a read of the array itself; no lemmas tried (the
// variants mbpr3 to mbpr5 tile 3 to 5 positions per iteration and are not translated)

method main() {
  var C: int;
  var i: int;
  var MINVAL: int;
  var V2: int;
  var V1: int;
  var a: array<int, int>;
  C := *;
  if C > 1 {
    MINVAL := 2;
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
      a := a[i * 2 - 1 := a[i * 2 - 1]];
      i := i + 1;
    }
    i := 1;
    while i <= C / 2 {
      if V1 >= MINVAL {
        a := a[i * 2 - 1 := V1];
      } else {
        a := a[i * 2 - 1 := 0];
      }
      a := a[i * 2 - 2 := a[i * 2 - 2]];
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
//   forall a₆: array<int, int>, C₇: int, n₁₀: int, K₁₂: Trace<int>,
//          I₁₄: Trace<int>, n₁₉: int, n₂₇: int, K₂₉: Trace<int>,
//          I₃₀: Trace<int> ::
//     1 < C₇
//       && C₇ % 2 == 0
//       && K₁₂ == counter(0, 1, n₁₀)
//       && I₁₄ == counter(1, 1, n₁₀)
//       && (n₁₀ == 0 || 0 < C₇ / 2 && n₁₀ == C₇ / 2)
//       && 0 <= n₁₀
//       && C₇ / 2 <= n₁₀
//       && (n₁₉ == 0 || 0 < C₇ / 2 && n₁₉ == C₇ / 2)
//       && 0 <= n₁₉
//       && C₇ / 2 <= n₁₉
//       && K₂₉ == counter(0, 1, n₂₇)
//       && I₃₀ == counter(0, 1, n₂₇)
//       && invs(for ⌊K₂₉⌋, ⌊I₃₀⌋
//               check k₂₈, i₂₆ ::
//                 2
//                   <= (if occurs(k₂₈, ⌊counter(1, 2, n₁₉)⌋)
//                       then 0
//                       else if occurs(k₂₈, maps(for ⌊K₁₂⌋, ⌊I₁₄⌋
//                                                yield k₁₁, i₉ ::
//                                                  2 * k₁₁))
//                       then 3
//                       else a₆[k₂₈])
//                   || (if occurs(k₂₈, ⌊counter(1, 2, n₁₉)⌋)
//                       then 0
//                       else if occurs(k₂₈, maps(for ⌊K₁₂⌋, ⌊I₁₄⌋
//                                                yield k₁₁, i₉ ::
//                                                  2 * k₁₁))
//                       then 3
//                       else a₆[k₂₈])
//                     == 0)
//       && 0 <= n₂₇ < C₇
//       ==> 2
//         <= (if occurs(n₂₇, ⌊counter(1, 2, n₁₉)⌋)
//             then 0
//             else if occurs(n₂₇, maps(for ⌊K₁₂⌋, ⌊I₁₄⌋ yield k₁₁, i₉ :: 2 * k₁₁))
//             then 3
//             else a₆[n₂₇])
//         || (if occurs(n₂₇, ⌊counter(1, 2, n₁₉)⌋)
//             then 0
//             else if occurs(n₂₇, maps(for ⌊K₁₂⌋, ⌊I₁₄⌋ yield k₁₁, i₉ :: 2 * k₁₁))
//             then 3
//             else a₆[n₂₇])
//           == 0
