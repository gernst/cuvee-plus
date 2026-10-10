// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-invgen/half_2.dfy
// SV-COMP loop-invgen/half_2.yml (expected: safe), translated from the C program by hand: k
// counts down from n once for every two steps of i up to n, and then n / 2 more times, staying positive before each
// step
//
// findings: open: the number of iterations n₈ of the first loop, with steps of 2 for i, is bounded by facts with
// the coefficient 2, n₅ <= 2 * n₈ and 2 * k < n₅ in all iterations, which the difference constraints of the
// simplifier do not combine (see TODO.md); no lemmas tried

method main() {
  var n: int;
  var i: int;
  var k: int;
  var j: int;
  n := *;
  k := n;
  i := 0;
  while i < n {
    k := k - 1;
    i := i + 2;
  }
  j := 0;
  while j < quot(n, 2) {
    assert k > 0;
    k := k - 1;
    j := j + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall n₅: int, n₈: int, K₁₀: Trace<int>, K₁₁: Trace<int>, I₁₂: Trace<int>,
//          n₁₇: int ::
//     n₅ <= 1000000
//       && K₁₀ == counter(0, 1, n₈)
//       && K₁₁ == counter(n₅, -1, n₈)
//       && I₁₂ == counter(0, 2, n₈)
//       && invs(for ⌊K₁₀⌋, ⌊K₁₁⌋, ⌊I₁₂⌋ check k₉, k₆, i₇ :: 2 * k₉ < n₅)
//       && 0 <= n₈
//       && n₅ <= 2 * n₈
//       && (n₁₇ == 0 || n₈ < n₅ && n₁₇ + n₈ == n₅)
//       && 0 <= n₁₇ < n₅ / 2
//       ==> n₁₇ + n₈ < n₅
