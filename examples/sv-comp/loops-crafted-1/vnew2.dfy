// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/vnew2.dfy
// SV-COMP loops-crafted-1/vnew2.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: i, j, k step by 3 up to n, and are checked to be equal and not a multiple of SIZE + 2
//
// findings: the functions truth, quotient, and remainder of the C prelude in the output of -print dfy are written
// as != 0, /, and % on the nonnegative values, and the havoc of unsigned values, printed as spec, as havoc and
// assume; open: the three counters are equal, but i % (SIZE + 2) != 0 needs that i, a multiple of 3 up to SIZE + 2,
// is below SIZE + 2, i.e., the bound at the last iteration with a remainder (see vnew1); no lemmas tried

var SIZE: int;

method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0
{
  var n: int, i: int, k: int, j: int;
  SIZE := 20000001;
  n := *;
  assume 0 <= n;
  if !(n <= SIZE) {
    result := 0;
    return;
  }
  k := 0;
  j := k;
  i := j;
  while i < n {
    i := i + 3;
    j := j + 3;
    k := k + 3;
  }
  if n > 0 {
    assert i == j == k && ((((i) % (SIZE + 2))) != 0);
  }
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// goal
//   forall n₆: int, n₁₀: int, K₁₂: Trace<int>, I₁₃: Trace<int>, J₁₄: Trace<int>,
//          K₁₅: Trace<int> ::
//     !(n₆ <= 20000001
//         && K₁₂ == counter(0, 1, n₁₀)
//         && I₁₃ == counter(0, 3, n₁₀)
//         && J₁₄ == counter(0, 3, n₁₀)
//         && K₁₅ == counter(0, 3, n₁₀)
//         && invs(for ⌊K₁₂⌋, ⌊I₁₃⌋, ⌊J₁₄⌋, ⌊K₁₅⌋
//                 check k₁₁, i₇, j₈, k₉ ::
//                   3 * k₁₁ < n₆)
//         && 0 <= n₁₀
//         && n₆ <= 3 * n₁₀
//         && 0 < n₆
//         && 3 * n₁₀ % 20000003 == 0)
