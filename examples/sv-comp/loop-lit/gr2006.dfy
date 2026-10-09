// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/gr2006.dfy
// SV-COMP ReachSafety-Loops/loop-lit/gr2006.yml (expected: safe), translated from the C program by hand: y counts
// up while x < 50 and then down, the loop leaves when y becomes negative, at x == 100, which is checked
//
// findings: open: y counts up while x < 50 and then down, until it becomes negative, a two-phase counter whose exit
// x == 100 needs the closed form of y over both phases (see phases_1-1, Mono1_1-2 for counters with phases); no
// lemmas tried

method main() {
  var x: int;
  var y: int;
  x := 0;
  y := 0;
  while true {
    if x < 50 {
      y := y + 1;
    } else {
      y := y - 1;
    }
    if y < 0 {
      break;
    }
    x := x + 1;
  }
  assert x == 100;
}

// remaining goals of -teq -simplify:
// goal
//   forall y₁₀: int, n₅: int, K₇: Trace<int>, Y₈: Trace<int>, X₉: Trace<int> ::
//     K₇ == counter(0, 1, n₅)
//       && y₁₀ == current(Y₈)
//       && Y₈
//         == trace(0, for ⌊K₇⌋, ⌊X₉⌋
//                     do y₃, k₆, x₄ ::
//                       case k₆ < 50 && 0 <= y₃ + 1 => y₃ + 1
//                       case 50 <= k₆ && 1 <= y₃ => y₃ + -1)
//       && X₉ == counter(0, 1, n₅)
//       && invs(for ⌊K₇⌋, ⌊Y₈⌋, ⌊X₉⌋
//               check k₆, y₃, x₄ ::
//                 k₆ < 50 && 0 <= y₃ + 1 || 50 <= k₆ && 1 <= y₃)
//       && 0 <= n₅
//       ==> (50 <= n₅ && y₁₀ < 1 ==> n₅ == 100) && !(n₅ < 50 && y₁₀ + 1 < 0)
