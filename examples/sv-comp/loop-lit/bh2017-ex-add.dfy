// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/bh2017-ex-add.dfy
// SV-COMP ReachSafety-Loops/loop-lit/bh2017-ex-add.yml (expected: safe), translated from the C program by hand: two
// counters m and n are incremented nondeterministically up to 60 and reset to 0 there, and are checked to stay at
// most 60
//
// findings: open: two counters that count up to 60 and are reset there, in nondeterministic iterations, a trace
// with three cases whose bound 60 needs an interval invariant of a counter with resets, like the interval
// invariants of benchmark51 but with the reset as a case; the second counter depends on the cases of the first,
// which -teq merges into its guards; no lemmas tried

method main() {
  var m: int;
  var n: int;
  var b: int;
  var c: int;
  m := 0;
  n := 0;
  while true {
    assert m <= 60;
    assert n <= 60;
    b := *;
    c := *;
    if b != 0 && c != 0 {
      if m < 60 {
        m := m + 1;
      } else {
        assert m == 60;
        m := 0;
      }
    }
    b := *;
    c := *;
    if b != 0 && c != 0 {
      if n < 60 {
        n := n + 1;
      } else {
        assert n == 60;
        n := 0;
      }
    }
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall m₃₄: int, n₃₅: int, n₂₅: int, K₂₇: Trace<int>, M₃₀: Trace<int>,
//          N₃₁: Trace<int>, B?₁₇: seq<int>, C?₁₈: seq<int>, B?₁₉: seq<int>,
//          C?₂₀: seq<int>, B?₂₁: seq<int>, C?₂₂: seq<int>, B?₂₃: seq<int>,
//          C?₂₄: seq<int> ::
//     K₂₇ == counter(0, 1, n₂₅)
//       && m₃₄ == current(M₃₀)
//       && n₃₅ == current(N₃₁)
//       && M₃₀
//         == trace(0, for ⌊K₂₇⌋, B?₁₇, C?₁₈
//                     do m₇, k₂₆, b₉, c₁₀ ::
//                       case b₉ != 0 && c₁₀ != 0 && m₇ < 60 => m₇ + 1
//                       case b₉ != 0 && c₁₀ != 0 && 60 <= m₇ => 0
//                       case !(b₉ != 0 && c₁₀ != 0) => m₇)
//       && N₃₁
//         == trace(0, for ⌊K₂₇⌋,
//                         ⌊M₃₀⌋,
//                         B?₁₇,
//                         C?₁₈,
//                         B?₁₉,
//                         C?₂₀,
//                         B?₂₁,
//                         C?₂₂,
//                         B?₂₃,
//                         C?₂₄
//                     do n₈, k₂₆, m₇, b₉, c₁₀, b₁₁, c₁₄, b₁₂, c₁₅, b₁₃, c₁₆ ::
//                       case n₈ < 60
//                         && (b₉ != 0
//                               && c₁₀ != 0
//                               && (m₇ < 60 && b₁₁ != 0 && c₁₄ != 0
//                                     || 60 <= m₇ && b₁₂ != 0 && c₁₅ != 0)
//                               || !(b₉ != 0 && c₁₀ != 0)
//                                 && b₁₃ != 0
//                                 && c₁₆ != 0) => n₈ + 1
//                       case 60 <= n₈
//                         && (b₉ != 0
//                               && c₁₀ != 0
//                               && (m₇ < 60 && b₁₁ != 0 && c₁₄ != 0
//                                     || 60 <= m₇ && b₁₂ != 0 && c₁₅ != 0)
//                               || !(b₉ != 0 && c₁₀ != 0)
//                                 && b₁₃ != 0
//                                 && c₁₆ != 0) => 0
//                       case b₉ != 0
//                         && c₁₀ != 0
//                         && (m₇ < 60 && !(b₁₁ != 0 && c₁₄ != 0)
//                               || 60 <= m₇ && !(b₁₂ != 0 && c₁₅ != 0))
//                         || !(b₉ != 0 && c₁₀ != 0)
//                           && !(b₁₃ != 0 && c₁₆ != 0) => n₈)
//       && invs(for ⌊K₂₇⌋,
//                   ⌊M₃₀⌋,
//                   ⌊N₃₁⌋,
//                   B?₁₇,
//                   C?₁₈,
//                   B?₁₉,
//                   C?₂₀,
//                   B?₂₁,
//                   C?₂₂,
//                   B?₂₃,
//                   C?₂₄
//               check k₂₆, m₇, n₈, b₉, c₁₀, b₁₁, c₁₄, b₁₂, c₁₅, b₁₃, c₁₆ ::
//                 b₉ != 0
//                   && c₁₀ != 0
//                   && m₇ < 60
//                   && b₁₁ != 0
//                   && c₁₄ != 0
//                   && n₈ < 60
//                   || b₉ != 0
//                     && c₁₀ != 0
//                     && m₇ < 60
//                     && b₁₁ != 0
//                     && c₁₄ != 0
//                     && n₈ == 60
//                   || b₉ != 0
//                     && c₁₀ != 0
//                     && m₇ < 60
//                     && !(b₁₁ != 0 && c₁₄ != 0)
//                     && n₈ <= 60
//                   || b₉ != 0
//                     && c₁₀ != 0
//                     && b₁₂ != 0
//                     && c₁₅ != 0
//                     && n₈ < 60
//                     && m₇ == 60
//                   || b₉ != 0
//                     && c₁₀ != 0
//                     && b₁₂ != 0
//                     && c₁₅ != 0
//                     && m₇ == 60
//                     && n₈ == 60
//                   || b₉ != 0
//                     && c₁₀ != 0
//                     && !(b₁₂ != 0 && c₁₅ != 0)
//                     && m₇ == 60
//                     && n₈ <= 60
//                   || !(b₉ != 0 && c₁₀ != 0)
//                     && b₁₃ != 0
//                     && c₁₆ != 0
//                     && n₈ < 60
//                     && m₇ <= 60
//                   || !(b₉ != 0 && c₁₀ != 0)
//                     && b₁₃ != 0
//                     && c₁₆ != 0
//                     && m₇ <= 60
//                     && n₈ == 60
//                   || !(b₉ != 0 && c₁₀ != 0)
//                     && !(b₁₃ != 0 && c₁₆ != 0)
//                     && m₇ <= 60
//                     && n₈ <= 60)
//       && 0 <= n₂₅
//       ==> m₃₄ <= 60 && n₃₅ <= 60
