// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/sumt3.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/sumt3.yml (expected: safe), translated from the C program by hand: l
// counts to n, at most SIZE == 20000001, unsigned, and i, j, k count the values of l that are multiples of 3, even
// otherwise, and the others, which add up to l
//
// findings: i, j, k count the iterations of three exclusive conditions on k % 3 and k % 2, which teq.dfy introduces
// as counts of maps, two of them of disjunctions as false; their sum n needs inclusion-exclusion over counts, i.e.,
// lemmas whose left-hand side is a sum of two counts, and equal counts up to the names of their bound variables
// (see TODO.md); no lemma is added

method main() {
  var n: int;
  var i: int;
  var j: int;
  var k: int;
  var l: int;
  havoc n;
  assume 0 <= n <= 20000001;
  i := 0;
  j := 0;
  k := 0;
  l := 0;
  while l < n {
    if l % 3 == 0 {
      i := i + 1;
    } else if l % 2 == 0 {
      j := j + 1;
    } else {
      k := k + 1;
    }
    l := l + 1;
  }
  assert i + j + k == l;
}

// remaining goals of -teq -simplify:
// goal
//   forall n₆: int, i₁₈: int, j₁₉: int, k₂₀: int, n₁₁: int, K₁₃: Trace<int>,
//          L₁₇: Trace<int> ::
//     0 <= n₆ <= 20000001
//       && K₁₃ == counter(0, 1, n₁₁)
//       && i₁₈ == count(0, maps(for ⌊K₁₃⌋, ⌊L₁₇⌋ yield k₁₂, l₁₀ :: k₁₂ % 3))
//       && j₁₉
//         == count(false, maps(for ⌊K₁₃⌋, ⌊L₁₇⌋
//                              yield k₁₂, l₁₀ ::
//                                k₁₂ % 3 == 0 || k₁₂ % 2 != 0))
//       && k₂₀
//         == count(false, maps(for ⌊K₁₃⌋, ⌊L₁₇⌋
//                              yield k₁₂, l₁₀ ::
//                                k₁₂ % 3 == 0 || k₁₂ % 2 == 0))
//       && L₁₇ == counter(0, 1, n₁₁)
//       && (n₁₁ == 0 || 0 < n₆ && n₁₁ == n₆)
//       && n₆ <= n₁₁
//       ==> i₁₈ + j₁₉ + k₂₀ == n₁₁
