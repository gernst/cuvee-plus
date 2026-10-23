// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/nla-digbench/cohencu-ll.dfy
// SV-COMP nla-digbench/cohencu-ll.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x == n^3 is computed by finite differences y and z, with the invariants checked in and
// after the loop
//
// findings: open: the cube by finite differences nests sums of sums (x == sum of y, y == sums of z, z a counter),
// whose closed forms need sums of squares and halving lemmas for each polynomial

method assume_abort_if_not(cond: int) {
  if !((cond) != 0) {
    assume false;
  }
}

method main() returns (result: int) {
  var a: int, n: int, x: int, y: int, z: int;
  a := *;
  assume 0 <= a;
  n := 0;
  x := 0;
  y := 1;
  z := 6;
  while ((1) != 0) {
    assert z == 6 * n + 6;
    assert y == 3 * n * n + 3 * n + 1;
    assert x == n * n * n;
    assert y * z - 18 * x - 12 * y + 2 * z - 6 == 0;
    assert z * z - 12 * y - 6 * z + 12 == 0;
    if !(n <= a) {
      break;
    }
    n := n + 1;
    x := x + y;
    y := y + z;
    z := z + 6;
  }
  assert z == 6 * n + 6;
  assert 6 * a * x - x * z + 12 * x == 0;
  assert a * z - 6 * a - 2 * y + 2 * z - 10 == 0;
  assert 2 * y * y - 3 * x * z - 18 * x - 10 * y + 3 * z - 10 == 0;
  assert z * z - 12 * y - 6 * z + 12 == 0;
  assert y * z - 18 * x - 12 * y + 2 * z - 6 == 0;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// goal
//   forall a₆: int, x₁₉: int, n₁₁: int, K₁₃: Trace<int>, N₁₄: Trace<int>,
//          X₁₅: Trace<int>, Y₁₆: Trace<int>, Z₁₇: Trace<int> ::
//     0 <= a₆
//       && K₁₃ == counter(0, 1, n₁₁)
//       && x₁₉ == sum(⌊Y₁₆⌋)
//       && N₁₄ == counter(0, 1, n₁₁)
//       && X₁₅ == sums(0, ⌊Y₁₆⌋)
//       && Y₁₆ == sums(1, ⌊Z₁₇⌋)
//       && Z₁₇ == counter(6, 6, n₁₁)
//       && n₁₁ < a₆ + 2
//       && invs(for ⌊K₁₃⌋, ⌊N₁₄⌋, ⌊Z₁₇⌋
//               check k₁₂, n₇, z₁₀ ::
//                 (6 * k₁₂ + 6 * k₁₂ * k₁₂) / 2 == 3 * k₁₂ + 3 * k₁₂ * k₁₂)
//       && invs(for ⌊K₁₃⌋, ⌊N₁₄⌋, ⌊X₁₅⌋, ⌊Z₁₇⌋
//               check k₁₂, n₇, x₈, z₁₀ ::
//                 x₈ == k₁₂ * k₁₂ * k₁₂)
//       && invs(for ⌊K₁₃⌋, ⌊N₁₄⌋, ⌊Z₁₇⌋
//               check k₁₂, n₇, z₁₀ ::
//                 (6 * k₁₂ + 6 * k₁₂ * k₁₂) / 2 * k₁₂ + 3 * k₁₂
//                   == (6 * k₁₂ + 6 * k₁₂ * k₁₂) / 2 + 3 * k₁₂ * k₁₂ * k₁₂)
//       && invs(for ⌊K₁₃⌋, ⌊N₁₄⌋, ⌊Z₁₇⌋
//               check k₁₂, n₇, z₁₀ ::
//                 3 * k₁₂ + 3 * k₁₂ * k₁₂ == (6 * k₁₂ + 6 * k₁₂ * k₁₂) / 2)
//       && 0 <= n₁₁
//       ==> (6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2 == 3 * n₁₁ + 3 * n₁₁ * n₁₁
//         && x₁₉ == n₁₁ * n₁₁ * n₁₁
//         && (6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2 * n₁₁ + 3 * n₁₁
//           == (6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2 + 3 * n₁₁ * n₁₁ * n₁₁
//         && 3 * n₁₁ + 3 * n₁₁ * n₁₁ == (6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2
//         && (a₆ < n₁₁
//               ==> a₆ * n₁₁ * n₁₁ * n₁₁ + n₁₁ * n₁₁ * n₁₁
//                 == n₁₁ * n₁₁ * n₁₁ * n₁₁
//                 && 3 * a₆ * n₁₁ + 6 * n₁₁ == (6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2
//                 && (6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2
//                   * ((6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2)
//                   + 9 * n₁₁
//                   == 3 * ((6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2)
//                     + 18 * n₁₁ * n₁₁ * n₁₁
//                     + 9 * n₁₁ * n₁₁ * n₁₁ * n₁₁
//                 && 3 * n₁₁ + 3 * n₁₁ * n₁₁ == (6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2
//                 && (6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2 * n₁₁ + 3 * n₁₁
//                   == (6 * n₁₁ + 6 * n₁₁ * n₁₁) / 2 + 3 * n₁₁ * n₁₁ * n₁₁)
