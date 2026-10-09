// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/iftelse.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/iftelse.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: i steps by 3 up to n, and j or k by 3 depending on the parity of i, and i / 2 <= j is
// checked (unsigned int is int)
//
// findings: the functions truth, quotient, and remainder of the C prelude in the output of -print dfy are written
// as != 0, /, and % on the nonnegative values, and the havoc of unsigned values, printed as spec, as havoc and
// assume; open: i steps by 3, and j or k by 3 depending on the parity of i, whose closed form needs counts of the
// parities of 3, 6, 9, ..., i.e., remainders of a counter with step 3 (see half, sumt2); no lemmas tried

var SIZE: int;

method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0
{
  SIZE := 20000001;
  {
    var n: int, i: int, k: int, j: int;
    n := *;
    assume 0 <= n;
    if !(n <= SIZE) {
      result := 0;
      return;
    }
    {
      {
        k := 0;
        j := k;
      }
      i := j;
    }
    while i < n {
      i := i + 3;
      if ((((i) % (2))) != 0) {
        j := j + 3;
      } else {
        k := k + 3;
      }
      if n > 0 {
        assert ((i) / (2)) <= j;
      }
    }
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall n₆: int, j₁₇: int, n₁₀: int, K₁₂: Trace<int>, I₁₃: Trace<int>,
//          J₁₄: Trace<int> ::
//     0 <= n₆ <= 20000001
//       && K₁₂ == counter(0, 1, n₁₀)
//       && j₁₇ == current(J₁₄)
//       && I₁₃ == counter(0, 3, n₁₀)
//       && J₁₄
//         == trace(0, for ⌊K₁₂⌋, ⌊I₁₃⌋
//                     do j₈, k₁₁, i₇ ::
//                       case (k₁₁ + 1) % 2 != 0 => j₈ + 3
//                       case (k₁₁ + 1) % 2 == 0 => j₈)
//       && invs(for ⌊K₁₂⌋, ⌊I₁₃⌋ check k₁₁, i₇ :: 3 * k₁₁ < n₆)
//       && invs(for ⌊K₁₂⌋, ⌊I₁₃⌋, ⌊J₁₄⌋
//               check k₁₁, i₇, j₈ ::
//                 (k₁₁ + 1) % 2 != 0 && 0 < n₆ && (3 * k₁₁ + 3) / 2 <= j₈ + 3
//                   || (k₁₁ + 1) % 2 != 0 && n₆ == 0
//                   || (k₁₁ + 1) % 2 == 0 < n₆ && (3 * k₁₁ + 3) / 2 <= j₈
//                   || (k₁₁ + 1) % 2 == 0 && n₆ == 0)
//       && 0 <= n₁₀
//       && 3 * n₁₀ < n₆
//       ==> ((n₁₀ + 1) % 2 != 0 && 0 < n₆ ==> (3 * n₁₀ + 3) / 2 <= j₁₇ + 3)
//         && ((n₁₀ + 1) % 2 == 0 < n₆ ==> (3 * n₁₀ + 3) / 2 <= j₁₇)
