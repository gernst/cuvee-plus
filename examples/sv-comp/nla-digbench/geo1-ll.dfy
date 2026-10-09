// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/geo1-ll.dfy
// SV-COMP ReachSafety-Loops/nla-digbench/geo1-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy, where the function number of the C prelude is written as a conditional: a geometric series x
// accumulates y, which is multiplied by z, and the closed form is checked
//
// findings: open: a geometric series, whose closed form needs powers, which teq.dfy has for geometric sequences
// only in specific forms (see underapprox_1-2); no lemmas tried

method assume_abort_if_not(cond: int) {
  {
    if !((cond) != 0) {
      assume false;
    }
  }
}

method main() returns (result: int) {
  {
    var z: int, k: int, x: int, y: int, c: int;
    havoc z;
    havoc k;
    assume_abort_if_not((if z >= 1 then 1 else 0));
    assume_abort_if_not((if k >= 1 then 1 else 0));
    x := 1;
    y := z;
    c := 1;
    while ((1) != 0) {
      assert x * z - x - y + 1 == 0;
      if !(c < k) {
        break;
      }
      c := c + 1;
      x := x * z + 1;
      y := y * z;
    }
    x := x * (z - 1);
    assert 1 + x - y == 0;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall z₆: int, k₇: int, x₅₄: int, y₅₅: int, n₄₇: int, K₄₉: Trace<int>,
//          C₅₀: Trace<int>, X₅₁: Trace<int>, Y₅₂: Trace<int> ::
//     (if 1 <= z₆ then 1 else 0) != 0
//       && (if 1 <= k₇ then 1 else 0) != 0
//       && K₄₉ == counter(0, 1, n₄₇)
//       && x₅₄ == current(X₅₁)
//       && y₅₅ == current(Y₅₂)
//       && C₅₀ == counter(1, 1, n₄₇)
//       && X₅₁ == trace(1, for ⌊K₄₉⌋, ⌊C₅₀⌋ do x₄₅, k₄₈, c₄₄ :: x₄₅ * z₆ + 1)
//       && Y₅₂ == trace(z₆, for ⌊K₄₉⌋, ⌊C₅₀⌋ do y₄₆, k₄₈, c₄₄ :: y₄₆ * z₆)
//       && (n₄₇ == 0 || 1 < k₇ && n₄₇ < k₇)
//       && invs(for ⌊K₄₉⌋, ⌊C₅₀⌋, ⌊X₅₁⌋, ⌊Y₅₂⌋
//               check k₄₈, c₄₄, x₄₅, y₄₆ ::
//                 x₄₅ * z₆ + 1 == x₄₅ + y₄₆)
//       && 0 <= n₄₇
//       ==> x₅₄ * z₆ + 1 == x₅₄ + y₅₅
