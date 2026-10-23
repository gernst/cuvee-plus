// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-cav19/array_min_and_copy_shift_sum_add.dfy
// SV-COMP array-cav19/array_min_and_copy_shift_sum_add.yml (expected: safe), translated from the C program by hand:
// j becomes the minimum of an initial value and the elements a[i], which are assumed bounded, b[i] = a[i] - j,
// and the sum k of b[i] + i is checked to be nonnegative
//
// findings: teq.dfy summarizes j as current(mins(j, selects(a, ...))); open: the sum of a[k] - j over the
// iterations needs each a[k] to be at least the minimum, the sum of nonnegative values to be nonnegative, and the
// conditional k < n₂₀ inside the sum needs n₂₀ == n₂₉, which follows from (n == 0 || 0 < N && n == N) for both only
// by a case split of the hypotheses (see TODO.md); no lemmas tried

method main() {
  var N: int;
  var i: int;
  var j: int;
  var k: int;
  var a: array<int, int>;
  var b: array<int, int>;
  j := *;
  k := 0;
  N := *;
  i := 0;
  while i < N {
    if j > a[i] {
      j := a[i];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[i := a[i] - j];
    i := i + 1;
  }
  i := 0;
  while i < N {
    k := k + b[i] + i;
    i := i + 1;
  }
  assert k >= 0;
}

// remaining goals of -teq -simplify:
// goal
//   forall a₅: array<int, int>, b₆: array<int, int>, j₇: int, N₈: int, j₁₆: int,
//          n₁₁: int, K₁₃: Trace<int>, J₁₄: Trace<int>, I₁₅: Trace<int>, n₂₀: int,
//          n₂₉: int, K₃₁: Trace<int> ::
//     j₇ < 10000
//       && 0 < j₇ + 10000
//       && N₈ < 10000
//       && 0 < N₈ + 10000
//       && K₁₃ == counter(0, 1, n₁₁)
//       && j₁₆ == current(J₁₄)
//       && J₁₄ == mins(j₇, selects(a₅, ⌊I₁₅⌋))
//       && I₁₅ == counter(0, 1, n₁₁)
//       && (n₁₁ == 0 || 0 < N₈ && n₁₁ == N₈)
//       && invs(for ⌊K₁₃⌋, ⌊I₁₅⌋ check k₁₂, i₁₀ :: a₅[k₁₂] < 10000)
//       && invs(for ⌊K₁₃⌋, ⌊I₁₅⌋ check k₁₂, i₁₀ :: 0 < a₅[k₁₂] + 10000)
//       && 0 <= n₁₁
//       && N₈ <= n₁₁
//       && (n₂₀ == 0 || 0 < N₈ && n₂₀ == N₈)
//       && 0 <= n₂₀
//       && N₈ <= n₂₀
//       && K₃₁ == counter(0, 1, n₂₉)
//       && (n₂₉ == 0 || 0 < N₈ && n₂₉ == N₈)
//       && 0 <= n₂₉
//       && N₈ <= n₂₉
//       ==> 0
//         <= (-n₂₉ + n₂₉ * n₂₉) / 2
//           + sum(maps(for ⌊K₃₁⌋
//                      yield k₃₀ ::
//                        if k₃₀ < n₂₀ then a₅[k₃₀] + -j₁₆ else b₆[k₃₀]))
