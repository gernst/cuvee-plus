// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-acceleration/phases_2-2.dfy
// SV-COMP loop-acceleration/phases_2-2.yml (expected: safe), translated from the C program by
// hand: x starts at 1 and is squared while that stays below y, then incremented, until it reaches y > 0, which is
// checked (unsigned int is int)
//
// findings: open: the value is squared while x < y / x and incremented otherwise, until it reaches y; the goal x <=
// y needs that each update from below y stays at most y, the bound at the last iteration of a non-linear update,
// for which no generic closed form is known (see phases_1-1 for the linear case)

method main() {
  var x: int;
  var y: int;
  x := 1;
  y := *;
  assume y >= 0;
  if !(y > 0) {
    return;
  }
  while x < y {
    if x < quot(y, x) {
      x := x * x;
    } else {
      x := x + 1;
    }
  }
  assert x == y;
}

// remaining goals of -teq -simplify:
// goal
//   forall y₃: int, x₉: int, n₅: int, K₇: Trace<int>, X₈: Trace<int> ::
//     !(0 < y₃
//         && K₇ == counter(0, 1, n₅)
//         && x₉ == current(X₈)
//         && X₈
//           == trace(1, for ⌊K₇⌋
//                       do x₄, k₆ ::
//                         case x₄ < y₃ / x₄ => x₄ * x₄
//                         case y₃ / x₄ <= x₄ => x₄ + 1)
//         && invs(for ⌊K₇⌋, ⌊X₈⌋ check k₆, x₄ :: x₄ < y₃)
//         && 0 <= n₅
//         && y₃ < x₉)
