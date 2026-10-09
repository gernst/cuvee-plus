// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/ifeqn1.dfy
// SV-COMP array-fpi/ifeqn1.yml (expected: safe), translated from the C program by hand: as eqn1,
// with the initial elements set in the first iteration of the loops: a holds 2, 4, ..., b the partial sums of a
// plus 1, which are checked to be i * i + i + 1 (ifeqn2 to ifeqn5 are variants)
//
// findings: the loop variable has the cases i == 0 => 1 and i != 0 => i + 1, which agree, joined by a lemma into
// the counter (a variant of that of copysome1-1), after which the simplifier identifies i with the counter k of the
// iterations; open: the recurrence with the case k == 0 for the first element reads a[k - 1], and a pattern with a
// sum over the bound variable k is not matched (as for ifcomp, see TODO.md), which a lemma like that of eqn1 for
// this form needs (tried, it applies to stores without the read); the variants ifeqn2 to ifeqn5 are not translated
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  N := *;
  assume 0 < N <= 536870911;
  i := 0;
  while i < N {
    if i == 0 {
      a := a[0 := 2];
    } else {
      a := a[i := a[i - 1] + 2];
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
    assert b[i] == i * i + i + 1;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₃: array<int, int>, b₄: array<int, int>, N₅: int,
//          a₁₃: array<int, int>, K₁₀: Trace<int>, A₁₁: Trace<array<int, int>>,
//          I₁₂: Trace<int>, b₂₂: array<int, int>, K₁₉: Trace<int>,
//          B₂₀: Trace<array<int, int>>, I₂₁: Trace<int>, n₂₅: int,
//          K₂₇: Trace<int>, I₂₈: Trace<int> ::
//     N₅ <= 536870911
//       && K₁₀ == counter(0, 1, N₅)
//       && a₁₃ == current(A₁₁)
//       && A₁₁
//         == trace(a₃, for ⌊K₁₀⌋, ⌊I₁₂⌋
//                      do a₆, k₉, i₇ ::
//                        case k₉ == 0 => a₆[0 := 2]
//                        case k₉ != 0 => a₆[k₉ := a₆[k₉ + -1] + 2])
//       && I₁₂ == counter(0, 1, N₅)
//       && K₁₉ == counter(0, 1, N₅)
//       && b₂₂ == current(B₂₀)
//       && B₂₀
//         == trace(b₄, for ⌊K₁₉⌋, ⌊I₂₁⌋
//                      do b₁₅, k₁₈, i₁₆ ::
//                        case k₁₈ == 0 => b₁₅[0 := 1]
//                        case k₁₈ != 0 => b₁₅[
//                          k₁₈ :=
//                          a₁₃[k₁₈ + -1] + b₁₅[k₁₈ + -1]])
//       && I₂₁ == counter(0, 1, N₅)
//       && K₂₇ == counter(0, 1, n₂₅)
//       && I₂₈ == counter(0, 1, n₂₅)
//       && invs(for ⌊K₂₇⌋, ⌊I₂₈⌋
//               check k₂₆, i₂₄ ::
//                 b₂₂[k₂₆] == k₂₆ + k₂₆ * k₂₆ + 1)
//       && 0 <= n₂₅ < N₅
//       ==> b₂₂[n₂₅] == n₂₅ + n₂₅ * n₂₅ + 1
