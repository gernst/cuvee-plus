// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-industry-pattern/mod3.dfy
// SV-COMP ReachSafety-Loops/loop-industry-pattern/mod3.yml (expected: safe), translated from the C program by hand:
// x is raised to the next multiple of 3 if it is not one, with y = 0, and otherwise by 4 or 5 with y = 1; if y == 0
// at the end, x % 3 == 0 is checked; unsigned int is int without wrap-around, which keeps the remainders here, since
// the additions that end at a multiple of 3 do not exceed 2^32 - 1, itself a multiple of 3
//
// findings: open: y == 0 at the end means that the last iteration took one of the first two cases, which leave x at
// a multiple of 3; this needs the case of the last iteration of a trace, from the last value of the trace y, and
// the remainder of x after it, a closed form that teq.dfy has for the bound at the last iteration of counters only
// (see Mono1_1-2); no lemmas tried (the reducer variants mod3.c.v+... are the same program)

method main() {
  var x: int;
  var y: int;
  var b: int;
  havoc x;
  assume x >= 0;
  y := 1;
  havoc b;
  while b != 0 {
    if x % 3 == 1 {
      x := x + 2;
      y := 0;
    } else {
      if x % 3 == 2 {
        x := x + 1;
        y := 0;
      } else {
        havoc b;
        if b != 0 {
          x := x + 4;
          y := 1;
        } else {
          x := x + 5;
          y := 1;
        }
      }
    }
    havoc b;
  }
  if y == 0 {
    assert x % 3 == 0;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall x₄: int, b₅: int, x₂₅: int, n₁₉: int, K₂₁: Trace<int>, X₂₂: Trace<int>,
//          Y₂₃: Trace<int>, B₂₄: Trace<int>, B?₁₄: seq<int>, B?₁₅: seq<int>,
//          B?₁₆: seq<int>, B?₁₇: seq<int>, B?₁₈: seq<int> ::
//     0 <= x₄
//       && K₂₁ == counter(0, 1, n₁₉)
//       && x₂₅ == current(X₂₂)
//       && 0 == current(Y₂₃)
//       && 0 == current(B₂₄)
//       && X₂₂
//         == trace(x₄, for ⌊K₂₁⌋, B?₁₆
//                      do x₆, k₂₀, b₉ ::
//                        case x₆ % 3 == 1 => x₆ + 2
//                        case x₆ % 3 == 2 => x₆ + 1
//                        case x₆ % 3 != 1 && x₆ % 3 != 2 && b₉ != 0 => x₆ + 4
//                        case x₆ % 3 != 1 && x₆ % 3 != 2 && b₉ == 0 => x₆ + 5)
//       && Y₂₃
//         == trace(1, for ⌊K₂₁⌋, ⌊X₂₂⌋
//                     do y₇, k₂₀, x₆ ::
//                       case x₆ % 3 == 1 || x₆ % 3 == 2 => 0
//                       case x₆ % 3 != 1 && x₆ % 3 != 2 => 1)
//       && B₂₄
//         == trace(b₅, for ⌊K₂₁⌋, ⌊X₂₂⌋, B?₁₄, B?₁₅, B?₁₆, B?₁₇, B?₁₈
//                      do b₈, k₂₀, x₆, b₁₀, b₁₁, b₉, b₁₂, b₁₃ ::
//                        case x₆ % 3 == 1 => b₁₀
//                        case x₆ % 3 == 2 => b₁₁
//                        case x₆ % 3 != 1 && x₆ % 3 != 2 && b₉ != 0 => b₁₂
//                        case x₆ % 3 != 1 && x₆ % 3 != 2 && b₉ == 0 => b₁₃)
//       && invs(for ⌊K₂₁⌋, ⌊B₂₄⌋ check k₂₀, b₈ :: b₈ != 0)
//       && 0 <= n₁₉
//       ==> x₂₅ % 3 == 0
