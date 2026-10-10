// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/ps2-ll.dfy
// SV-COMP nla-digbench/ps2-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: y counts up to k and x accumulates y, and 2 x == y * y + y, as y * y - 2 x + y == 0, is checked in
// and after the loop (long long is int)
//
// findings: open: teq.dfy sums the values of y as (-n + n * n) / 2, and the remaining goal needs 2 * ((-n + n * n)
// / 2) == -n + n * n, i.e., that n * n - n is even; a lemma stating this in the normal form of the simplifier does
// not match the monomial 2 * (...) inside the equation, presumably since equations are normalized as differences of
// polynomials (see TODO.md); the variants of nla-digbench-scaling are not translated

method assume_abort_if_not(cond: int) {
  if !((cond) != 0) {
    assume false;
  }
}

method main() returns (result: int) {
  var k: int, y: int, x: int, c: int;
  k := *;
  y := 0;
  x := 0;
  c := 0;
  while ((1) != 0) {
    assert y * y - 2 * x + y == 0;
    if !(c < k) {
      break;
    }
    c := c + 1;
    y := y + 1;
    x := y + x;
  }
  assert y * y - 2 * x + y == 0;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// goal
//   forall k₅: int, n₉: int, K₁₁: Trace<int>, C₁₂: Trace<int>, Y₁₃: Trace<int>,
//          X₁₄: Trace<int> ::
//     K₁₁ == counter(0, 1, n₉)
//       && C₁₂ == counter(0, 1, n₉)
//       && Y₁₃ == counter(0, 1, n₉)
//       && X₁₄ == sums(0, maps(for ⌊K₁₁⌋ yield k₁₀ :: k₁₀ + 1))
//       && (n₉ == 0 || 0 < k₅ && n₉ <= k₅)
//       && invs(for ⌊K₁₁⌋, ⌊C₁₂⌋, ⌊Y₁₃⌋, ⌊X₁₄⌋
//               check k₁₀, c₆, y₇, x₈ ::
//                 k₁₀ + k₁₀ * k₁₀ == 2 * x₈)
//       && 0 <= n₉
//       ==> n₉ * n₉ == 2 * ((-n₉ + n₉ * n₉) / 2) + n₉
