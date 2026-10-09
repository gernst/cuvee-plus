// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/ncomp.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/ncomp.yml (expected: safe), translated from the C program by hand: as
// ifncomp, with the initial elements set before the loops from 1
//
// findings: open: three recurrences from 1, whose closed forms are 6 i + 6, 3 i * i + 3 i + 1 summed, and N + i * i
// * i, which needs the sums of linear and quadratic terms over counters, the latter of which teq.dfy does not sum
// (see the further ideas of the summary); no lemmas tried

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  havoc N;
  assume 0 < N <= 536870911;
  a := a[0 := 6];
  b := b[0 := 1];
  c := c[0 := N];
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + 6];
    i := i + 1;
  }
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + a[i - 1]];
    i := i + 1;
  }
  i := 1;
  while i < N {
    c := c[i := c[i - 1] + b[i - 1]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert c[i] == N + i * i * i;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₃: array<int, int>, b₄: array<int, int>, c₅: array<int, int>, N₆: int,
//          a₁₄: array<int, int>, n₉: int, K₁₁: Trace<int>,
//          A₁₂: Trace<array<int, int>>, I₁₃: Trace<int>, b₂₃: array<int, int>,
//          n₁₈: int, K₂₀: Trace<int>, B₂₁: Trace<array<int, int>>,
//          I₂₂: Trace<int>, c₃₂: array<int, int>, n₂₇: int, K₂₉: Trace<int>,
//          C₃₀: Trace<array<int, int>>, I₃₁: Trace<int>, n₃₅: int,
//          K₃₇: Trace<int>, I₃₈: Trace<int> ::
//     N₆ <= 536870911
//       && K₁₁ == counter(0, 1, n₉)
//       && a₁₄ == current(A₁₂)
//       && A₁₂
//         == trace(a₃[0 := 6], for ⌊K₁₁⌋, ⌊I₁₃⌋
//                              do a₇, k₁₀, i₈ ::
//                                a₇[i₈ := a₇[k₁₀] + 6])
//       && I₁₃ == counter(1, 1, n₉)
//       && (n₉ == 0 || 1 < N₆ && n₉ < N₆)
//       && N₆ <= n₉ + 1
//       && K₂₀ == counter(0, 1, n₁₈)
//       && b₂₃ == current(B₂₁)
//       && B₂₁
//         == trace(b₄[0 := 1], for ⌊K₂₀⌋, ⌊I₂₂⌋
//                              do b₁₆, k₁₉, i₁₇ ::
//                                b₁₆[i₁₇ := a₁₄[k₁₉] + b₁₆[k₁₉]])
//       && I₂₂ == counter(1, 1, n₁₈)
//       && (n₁₈ == 0 || 1 < N₆ && n₁₈ < N₆)
//       && N₆ <= n₁₈ + 1
//       && K₂₉ == counter(0, 1, n₂₇)
//       && c₃₂ == current(C₃₀)
//       && C₃₀
//         == trace(c₅[0 := N₆], for ⌊K₂₉⌋, ⌊I₃₁⌋
//                               do c₂₅, k₂₈, i₂₆ ::
//                                 c₂₅[i₂₆ := b₂₃[k₂₈] + c₂₅[k₂₈]])
//       && I₃₁ == counter(1, 1, n₂₇)
//       && (n₂₇ == 0 || 1 < N₆ && n₂₇ < N₆)
//       && N₆ <= n₂₇ + 1
//       && K₃₇ == counter(0, 1, n₃₅)
//       && I₃₈ == counter(0, 1, n₃₅)
//       && invs(for ⌊K₃₇⌋, ⌊I₃₈⌋
//               check k₃₆, i₃₄ ::
//                 c₃₂[k₃₆] == N₆ + k₃₆ * k₃₆ * k₃₆)
//       && 0 <= n₃₅ < N₆
//       ==> c₃₂[n₃₅] == N₆ + n₃₅ * n₃₅ * n₃₅
