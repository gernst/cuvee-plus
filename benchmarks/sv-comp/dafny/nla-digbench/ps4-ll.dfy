// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/ps4-ll.dfy
// SV-COMP nla-digbench/ps4-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: y counts up to k and x accumulates y^3, and 4 x == y^4 + 2 y^3 + y^2 is checked in and after the loop
//
// findings: open: needs the sum of cubes over a counter, as ps3-ll

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
    assert 4 * x - y * y * y * y - 2 * y * y * y - y * y == 0;
    if !(c < k) {
      break;
    }
    c := c + 1;
    y := y + 1;
    x := y * y * y + x;
  }
  assert k * y - y * y == 0;
  assert 4 * x - y * y * y * y - 2 * y * y * y - y * y == 0;
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
//       && X₁₄
//         == sums(0, maps(for ⌊K₁₁⌋
//                         yield k₁₀ ::
//                           3 * k₁₀ + 3 * k₁₀ * k₁₀ + k₁₀ * k₁₀ * k₁₀ + 1))
//       && (n₉ == 0 || 0 < k₅ && n₉ <= k₅)
//       && invs(for ⌊K₁₁⌋, ⌊C₁₂⌋, ⌊Y₁₃⌋, ⌊X₁₄⌋
//               check k₁₀, c₆, y₇, x₈ ::
//                 4 * x₈
//                   == k₁₀ * k₁₀ + 2 * k₁₀ * k₁₀ * k₁₀ + k₁₀ * k₁₀ * k₁₀ * k₁₀)
//       && 0 <= n₉
//       ==> 12 * ((-n₉ + n₉ * n₉) / 2)
//         + 4 * sum(maps(for ⌊K₁₁⌋ yield k₁₀ :: 3 * k₁₀ * k₁₀))
//         + 4 * sum(maps(for ⌊K₁₁⌋ yield k₁₀ :: k₁₀ * k₁₀ * k₁₀))
//         + 4 * n₉
//         == n₉ * n₉ + 2 * n₉ * n₉ * n₉ + n₉ * n₉ * n₉ * n₉
//         && (k₅ <= n₉
//               ==> k₅ * n₉ == n₉ * n₉
//                 && 12 * ((-n₉ + n₉ * n₉) / 2)
//                   + 4 * sum(maps(for ⌊K₁₁⌋ yield k₁₀ :: 3 * k₁₀ * k₁₀))
//                   + 4 * sum(maps(for ⌊K₁₁⌋ yield k₁₀ :: k₁₀ * k₁₀ * k₁₀))
//                   + 4 * n₉
//                   == n₉ * n₉ + 2 * n₉ * n₉ * n₉ + n₉ * n₉ * n₉ * n₉)
