// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/string_concat-noarr.dfy
// SV-COMP ReachSafety-Loops/loop-invgen/string_concat-noarr.yml (expected: safe), translated from the C program by
// hand: i counts nondeterministically, at most 100 times (else the program is stuck, i.e., assume false), then i
// and j count together, j at most 100 times, and i < 200 is checked
//
// findings: open: the goal n₃₉ + n₉ < 200 follows from n₃₉ < 100 and n₉ < 100, a sum of two variables, which is no
// difference constraint (as for seq-3, see TODO.md)

method main() {
  var i: int;
  var j: int;
  var b: int;
  i := 0;
  havoc b;
  while b != 0 && i < 1000000 {
    i := i + 1;
    havoc b;
  }
  if i >= 100 {
    assume false;
  }
  j := 0;
  havoc b;
  while b != 0 && i < 1000000 {
    i := i + 1;
    j := j + 1;
    havoc b;
  }
  if j >= 100 {
    assume false;
  }
  assert i < 200;
}

// remaining goals of -teq -simplify:
// goal
//   forall b₄: int, n₉: int, K₁₁: Trace<int>, I₁₂: Trace<int>, B₁₃: Trace<int>,
//          B?₈: seq<int>, b₁₈: int, b₄₇: int, n₃₉: int, K₄₁: Trace<int>,
//          I₄₂: Trace<int>, J₄₃: Trace<int>, B₄₄: Trace<int>, B?₃₈: seq<int> ::
//     K₁₁ == counter(0, 1, n₉)
//       && 0 == current(B₁₃)
//       && I₁₂ == counter(0, 1, n₉)
//       && B₁₃ == trace(b₄, for ⌊K₁₁⌋, B?₈ do b₆, k₁₀, b₇ :: b₇)
//       && invs(for ⌊K₁₁⌋, ⌊I₁₂⌋, ⌊B₁₃⌋ check k₁₀, i₅, b₆ :: b₆ != 0)
//       && 0 <= n₉ < 100
//       && K₄₁ == counter(0, 1, n₃₉)
//       && b₄₇ == current(B₄₄)
//       && I₄₂ == counter(n₉, 1, n₃₉)
//       && J₄₃ == counter(0, 1, n₃₉)
//       && B₄₄ == trace(b₁₈, for ⌊K₄₁⌋, B?₃₈ do b₃₆, k₄₀, b₃₇ :: b₃₇)
//       && invs(for ⌊K₄₁⌋, ⌊I₄₂⌋, ⌊J₄₃⌋, ⌊B₄₄⌋
//               check k₄₀, i₃₄, j₃₅, b₃₆ ::
//                 b₃₆ != 0)
//       && (n₃₉ == 0 || n₃₉ + n₉ < 1000001)
//       && 0 <= n₃₉ < 100
//       ==> b₄₇ != 0 && n₃₉ + n₉ < 1000000 || n₃₉ + n₉ < 200
