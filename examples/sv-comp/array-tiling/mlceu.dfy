// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/mlceu.dfy
// SV-COMP ReachSafety-Arrays/array-tiling/mlceu.yml (expected: unsafe), translated from the C program by hand:
// as mlceu2, but the sizes go up to 66060288 / 4, where i >> 16 > 250 holds for the last positions
//
// findings: unsafe: i >> 16 > 250 holds for the positions from 251 * 65536 = 16449536 on, below the bound 66060288
// / 4 of the size; open, as expected, also with the lemmas of mlceu2

method main() {
  var S: int;
  var i: int;
  var a: array<int, int>;
  havoc S;
  if S <= 0 {
    return;
  }
  assume S <= 66060288 / 4;
  i := 0;
  while i < S {
    if i / 65536 > 250 {
      a := a[i := 1];
    } else {
      a := a[i := 0];
    }
    i := i + 1;
  }
  i := 0;
  while i < S {
    assert a[i] == 0;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₃: array<int, int>, S₄: int, a₁₂: array<int, int>, K₉: Trace<int>,
//          A₁₀: Trace<array<int, int>>, I₁₁: Trace<int>, n₁₅: int,
//          K₁₇: Trace<int>, I₁₈: Trace<int> ::
//     S₄ <= 16515072
//       && K₉ == counter(0, 1, S₄)
//       && a₁₂ == current(A₁₀)
//       && A₁₀
//         == trace(a₃, for ⌊K₉⌋, ⌊I₁₁⌋
//                      do a₅, k₈, i₆ ::
//                        case 250 < k₈ / 65536 => a₅[k₈ := 1]
//                        case k₈ / 65536 <= 250 => a₅[k₈ := 0])
//       && I₁₁ == counter(0, 1, S₄)
//       && K₁₇ == counter(0, 1, n₁₅)
//       && I₁₈ == counter(0, 1, n₁₅)
//       && invs(for ⌊K₁₇⌋, ⌊I₁₈⌋ check k₁₆, i₁₄ :: a₁₂[k₁₆] == 0)
//       && 0 <= n₁₅ < S₄
//       ==> a₁₂[n₁₅] == 0
