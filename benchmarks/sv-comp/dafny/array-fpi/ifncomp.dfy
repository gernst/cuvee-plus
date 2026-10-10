// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/ifncomp.dfy
// SV-COMP array-fpi/ifncomp.yml (expected: safe), translated from the C program by hand: a holds
// 6, 12, ..., b the partial sums of a plus 1, c the partial sums of b plus N, which are checked to be N + i * i *
// i, with the initial elements set in the first iteration
//
// findings: open: as ifeqn1, three recurrences with the case i == 0, the third summing the second; additionally
// needs sums of squares over counters, which teq.dfy does not sum (see ncomp); no lemmas tried

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  N := *;
  assume 0 < N;
  i := 0;
  while i < N {
    if i == 0 {
      a := a[0 := 6];
    } else {
      a := a[i := a[i - 1] + 6];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      b := b[0 := 1];
    } else {
      b := b[i := b[i - 1] + a[i - 1]];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      c := c[0 := N];
    } else {
      c := c[i := c[i - 1] + b[i - 1]];
    }
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
//          a₁₄: array<int, int>, i₁₅: int, n₉: int, K₁₁: Trace<int>,
//          A₁₂: Trace<array<int, int>>, I₁₃: Trace<int>, b₂₃: array<int, int>,
//          i₂₄: int, n₁₈: int, K₂₀: Trace<int>, B₂₁: Trace<array<int, int>>,
//          I₂₂: Trace<int>, c₃₂: array<int, int>, i₃₃: int, n₂₇: int,
//          K₂₉: Trace<int>, C₃₀: Trace<array<int, int>>, I₃₁: Trace<int>,
//          n₃₅: int, K₃₇: Trace<int>, I₃₈: Trace<int> ::
//     N₆ <= 536870911
//       && K₁₁ == counter(0, 1, n₉)
//       && a₁₄ == current(A₁₂)
//       && i₁₅ == current(I₁₃)
//       && A₁₂
//         == trace(a₃, for ⌊K₁₁⌋, ⌊I₁₃⌋
//                      do a₇, k₁₀, i₈ ::
//                        case i₈ == 0 => a₇[0 := 6]
//                        case i₈ != 0 => a₇[i₈ := a₇[i₈ + -1] + 6])
//       && I₁₃
//         == trace(0, for ⌊K₁₁⌋
//                     do i₈, k₁₀ ::
//                       case i₈ == 0 => 1 case i₈ != 0 => i₈ + 1)
//       && invs(for ⌊K₁₁⌋, ⌊I₁₃⌋ check k₁₀, i₈ :: i₈ < N₆)
//       && 0 <= n₉
//       && N₆ <= i₁₅
//       && K₂₀ == counter(0, 1, n₁₈)
//       && b₂₃ == current(B₂₁)
//       && i₂₄ == current(I₂₂)
//       && B₂₁
//         == trace(b₄, for ⌊K₂₀⌋, ⌊I₂₂⌋
//                      do b₁₆, k₁₉, i₁₇ ::
//                        case i₁₇ == 0 => b₁₆[0 := 1]
//                        case i₁₇ != 0 => b₁₆[
//                          i₁₇ :=
//                          a₁₄[i₁₇ + -1] + b₁₆[i₁₇ + -1]])
//       && I₂₂
//         == trace(0, for ⌊K₂₀⌋
//                     do i₁₇, k₁₉ ::
//                       case i₁₇ == 0 => 1 case i₁₇ != 0 => i₁₇ + 1)
//       && invs(for ⌊K₂₀⌋, ⌊I₂₂⌋ check k₁₉, i₁₇ :: i₁₇ < N₆)
//       && 0 <= n₁₈
//       && N₆ <= i₂₄
//       && K₂₉ == counter(0, 1, n₂₇)
//       && c₃₂ == current(C₃₀)
//       && i₃₃ == current(I₃₁)
//       && C₃₀
//         == trace(c₅, for ⌊K₂₉⌋, ⌊I₃₁⌋
//                      do c₂₅, k₂₈, i₂₆ ::
//                        case i₂₆ == 0 => c₂₅[0 := N₆]
//                        case i₂₆ != 0 => c₂₅[
//                          i₂₆ :=
//                          b₂₃[i₂₆ + -1] + c₂₅[i₂₆ + -1]])
//       && I₃₁
//         == trace(0, for ⌊K₂₉⌋
//                     do i₂₆, k₂₈ ::
//                       case i₂₆ == 0 => 1 case i₂₆ != 0 => i₂₆ + 1)
//       && invs(for ⌊K₂₉⌋, ⌊I₃₁⌋ check k₂₈, i₂₆ :: i₂₆ < N₆)
//       && 0 <= n₂₇
//       && N₆ <= i₃₃
//       && K₃₇ == counter(0, 1, n₃₅)
//       && I₃₈ == counter(0, 1, n₃₅)
//       && invs(for ⌊K₃₇⌋, ⌊I₃₈⌋
//               check k₃₆, i₃₄ ::
//                 c₃₂[k₃₆] == N₆ + k₃₆ * k₃₆ * k₃₆)
//       && 0 <= n₃₅ < N₆
//       ==> c₃₂[n₃₅] == N₆ + n₃₅ * n₃₅ * n₃₅
