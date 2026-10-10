// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/mannadiv.dfy
// SV-COMP nla-digbench/mannadiv.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy, where the function number of the C prelude is written as a conditional: Manna's division of x1 by x2
// by repeated subtraction, with the invariant checked in and after the loop
//
// findings: open: division by repeated subtraction with three variables that are reset in a nested case split,
// whose invariant x1 == q * x2 + r is non-linear; no lemmas tried

method assume_abort_if_not(cond: int) {
  if !((cond) != 0) {
    assume false;
  }
}

method main() returns (result: int) {
  var x1: int, x2: int, y1: int, y2: int, y3: int;
  x1 := *;
  x2 := *;
  assume_abort_if_not((if x1 >= 0 then 1 else 0));
  assume_abort_if_not((if x2 != 0 then 1 else 0));
  y1 := 0;
  y2 := 0;
  y3 := x1;
  while ((1) != 0) {
    assert y1 * x2 + y2 + y3 == x1;
    if !(y3 != 0) {
      break;
    }
    if y2 + 1 == x2 {
      y1 := y1 + 1;
      y2 := 0;
      y3 := y3 - 1;
    } else {
      y2 := y2 + 1;
      y3 := y3 - 1;
    }
  }
  assert y1 * x2 + y2 == x1;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// goal
//   forall x1₆: int, x2₇: int, y1₅₃: int, y2₅₄: int, y3₅₅: int, n₄₇: int,
//          K₄₉: Trace<int>, Y1₅₀: Trace<int>, Y2₅₁: Trace<int>,
//          Y3₅₂: Trace<int> ::
//     (if 0 <= x1₆ then 1 else 0) != 0
//       && (if x2₇ != 0 then 1 else 0) != 0
//       && K₄₉ == counter(0, 1, n₄₇)
//       && y1₅₃ == count(x2₇, maps(for ⌊K₄₉⌋, ⌊Y2₅₁⌋ yield k₄₈, y2₄₅ :: y2₄₅ + 1))
//       && y2₅₄ == current(Y2₅₁)
//       && n₄₇ + y3₅₅ == x1₆
//       && Y1₅₀
//         == counts(0, x2₇, maps(for ⌊K₄₉⌋, ⌊Y2₅₁⌋ yield k₄₈, y2₄₅ :: y2₄₅ + 1))
//       && Y2₅₁
//         == trace(0, for ⌊K₄₉⌋, ⌊Y3₅₂⌋
//                     do y2₄₅, k₄₈, y3₄₆ ::
//                       case y2₄₅ + 1 == x2₇ => 0
//                       case y2₄₅ + 1 != x2₇ => y2₄₅ + 1)
//       && Y3₅₂ == counter(x1₆, -1, n₄₇)
//       && invs(for ⌊K₄₉⌋, ⌊Y3₅₂⌋ check k₄₈, y3₄₆ :: y3₄₆ != 0)
//       && invs(for ⌊K₄₉⌋, ⌊Y1₅₀⌋, ⌊Y2₅₁⌋, ⌊Y3₅₂⌋
//               check k₄₈, y1₄₄, y2₄₅, y3₄₆ ::
//                 x2₇ * y1₄₄ + y2₄₅ + y3₄₆ == x1₆)
//       && y3₅₅ <= x1₆
//       ==> x2₇ * y1₅₃ + y2₅₄ + y3₅₅ == x1₆
//         && (y3₅₅ == 0 ==> x2₇ * y1₅₃ + y2₅₄ == x1₆)
