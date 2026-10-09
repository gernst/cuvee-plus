// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/vnew1.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/vnew1.yml (expected: safe), translated from the C program by hand: k
// counts down from n, unsigned and at most SIZE == 20000001, once per step of 3 of i up to n, then once for each of
// n / 3 iterations, and is positive before each decrement
//
// findings: the first loop counts by 3 and decrements k, its iteration constraint 3 * k < n over the iterations is
// not accelerated, since the coefficient 3 is matched by no variable of a pattern (see TODO.md), and the goal needs
// the relation of the iterations to n / 3, which is integer division; no lemma is added

method main() {
  var n: int;
  var i: int;
  var k: int;
  var j: int;
  n := *;
  assume 0 <= n <= 20000001;
  k := n;
  i := 0;
  while i < n {
    k := k - 1;
    i := i + 3;
  }
  j := 0;
  while j < n / 3 {
    assert k > 0;
    k := k - 1;
    j := j + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall n₅: int, n₈: int, K₁₀: Trace<int>, K₁₁: Trace<int>, I₁₂: Trace<int>,
//          n₁₇: int ::
//     0 <= n₅ <= 20000001
//       && K₁₀ == counter(0, 1, n₈)
//       && K₁₁ == counter(n₅, -1, n₈)
//       && I₁₂ == counter(0, 3, n₈)
//       && invs(for ⌊K₁₀⌋, ⌊K₁₁⌋, ⌊I₁₂⌋ check k₉, k₆, i₇ :: 3 * k₉ < n₅)
//       && 0 <= n₈
//       && n₅ <= 3 * n₈
//       && (n₁₇ == 0 || n₈ < n₅ && n₁₇ + n₈ == n₅)
//       && 0 <= n₁₇ < n₅ / 3
//       ==> n₁₇ + n₈ < n₅
