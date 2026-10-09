// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/sumt4.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/sumt4.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: four counters count the remainders of l modulo 4, 3, 2, and their sum is checked to be l
//
// findings: the functions truth, quotient, and remainder of the C prelude in the output of -print dfy are written
// as != 0, /, and % on the nonnegative values, and the havoc of unsigned values, printed as spec, as havoc and
// assume; open: four counters of the remainders of l modulo 4, 3, 2 add up to l, which needs the counts over a case
// split on remainders to add up to the number of iterations (see sumt3); no lemmas tried (sumt5 to sumt9 are
// variants)

var SIZE: int;

method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0
{
  SIZE := 20000001;
  {
    var n: int, i: int, k: int, j: int, l: int, v4: int;
    n := 0;
    i := 0;
    k := 0;
    j := 0;
    l := 0;
    v4 := 0;
    havoc n;
    assume 0 <= n;
    if !(n <= SIZE) {
      result := 0;
      return;
    }
    while l < n {
      if !((((l) % (4))) != 0) {
        v4 := v4 + 1;
      } else if !((((l) % (3))) != 0) {
        i := i + 1;
      } else if !((((l) % (2))) != 0) {
        j := j + 1;
      } else {
        k := k + 1;
      }
      l := l + 1;
    }
    assert i + j + k + v4 == l;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall n₈: int, k₂₂: int, j₂₃: int, i₂₅: int, v4₂₆: int, n₁₄: int,
//          K₁₆: Trace<int>, L₁₉: Trace<int> ::
//     0 <= n₈ <= 20000001
//       && K₁₆ == counter(0, 1, n₁₄)
//       && k₂₂
//         == count(false, maps(for ⌊K₁₆⌋, ⌊L₁₉⌋
//                              yield k₁₅, l₁₁ ::
//                                k₁₅ % 4 == 0 || k₁₅ % 3 == 0 || k₁₅ % 2 == 0))
//       && j₂₃
//         == count(false, maps(for ⌊K₁₆⌋, ⌊L₁₉⌋
//                              yield k₁₅, l₁₁ ::
//                                k₁₅ % 4 == 0 || k₁₅ % 3 == 0 || k₁₅ % 2 != 0))
//       && i₂₅
//         == count(false, maps(for ⌊K₁₆⌋
//                              yield k₁₅ ::
//                                k₁₅ % 4 == 0
//                                  || k₁₅ % 3 != 0 && k₁₅ % 2 == 0
//                                  || k₁₅ % 3 != 0 && k₁₅ % 2 != 0))
//       && v4₂₆ == count(0, maps(for ⌊K₁₆⌋ yield k₁₅ :: k₁₅ % 4))
//       && L₁₉ == counter(0, 1, n₁₄)
//       && (n₁₄ == 0 || 0 < n₈ && n₁₄ == n₈)
//       && n₈ <= n₁₄
//       ==> i₂₅ + j₂₃ + k₂₂ + v4₂₆ == n₁₄
