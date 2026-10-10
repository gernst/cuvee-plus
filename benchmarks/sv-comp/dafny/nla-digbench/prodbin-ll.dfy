// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/prodbin-ll.dfy
// SV-COMP nla-digbench/prodbin-ll.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy, where the function number of the C prelude is written as a conditional: the product of a
// and b by binary multiplication, with the invariant checked in and after the loop
//
// findings: open: binary multiplication halves a and doubles b, whose closed forms need powers of 2 and the binary
// digits of a; no lemmas tried

method assume_abort_if_not(cond: int) {
  if !((cond) != 0) {
    assume false;
  }
}

method main() returns (result: int) {
  var a: int, b: int, x: int, y: int, z: int;
  a := *;
  b := *;
  assume_abort_if_not((if b >= 1 then 1 else 0));
  x := a;
  y := b;
  z := 0;
  while ((1) != 0) {
    assert z + x * y == a * b;
    if !(y != 0) {
      break;
    }
    if ((y) % (2)) == 1 {
      z := z + x;
      y := y - 1;
    }
    x := 2 * x;
    y := ((y) / (2));
  }
  assert z == a * b;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// goal
//   forall a₆: int, b₇: int, z₂₉: int, y₃₀: int, x₃₁: int, n₂₃: int,
//          K₂₅: Trace<int>, Z₂₆: Trace<int>, Y₂₇: Trace<int>, X₂₈: Trace<int> ::
//     (if 1 <= b₇ then 1 else 0) != 0
//       && K₂₅ == counter(0, 1, n₂₃)
//       && z₂₉ == current(Z₂₆)
//       && y₃₀ == current(Y₂₇)
//       && x₃₁ == current(X₂₈)
//       && Z₂₆
//         == trace(0, for ⌊K₂₅⌋, ⌊Y₂₇⌋, ⌊X₂₈⌋
//                     do z₂₀, k₂₄, y₂₁, x₂₂ ::
//                       case y₂₁ % 2 == 1 => a₆ * b₇ + x₂₂ + -(x₂₂ * y₂₁)
//                       case y₂₁ % 2 != 1 => z₂₀)
//       && Y₂₇
//         == trace(b₇, for ⌊K₂₅⌋
//                      do y₂₁, k₂₄ ::
//                        case y₂₁ % 2 == 1 => (y₂₁ + -1) / 2
//                        case y₂₁ % 2 != 1 => y₂₁ / 2)
//       && X₂₈ == trace(a₆, for ⌊K₂₅⌋ do x₂₂, k₂₄ :: 2 * x₂₂)
//       && invs(for ⌊K₂₅⌋, ⌊Y₂₇⌋ check k₂₄, y₂₁ :: y₂₁ != 0)
//       && invs(for ⌊K₂₅⌋, ⌊Z₂₆⌋, ⌊Y₂₇⌋, ⌊X₂₈⌋
//               check k₂₄, z₂₀, y₂₁, x₂₂ ::
//                 x₂₂ * y₂₁ + z₂₀ == a₆ * b₇)
//       && 0 <= n₂₃
//       ==> x₃₁ * y₃₀ + z₂₉ == a₆ * b₇
