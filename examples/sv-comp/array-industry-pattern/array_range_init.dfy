// ./Cuvee.sh -teq -simplify examples/sv-comp/array-industry-pattern/array_range_init.dfy
// SV-COMP array-industry-pattern/array_range_init.yml (expected: unsafe), translated from the C program by hand:
// a[i] = 10 for 0 <= i <= 10000 and 0 otherwise, and all are checked to be 10
//
// findings: unsafe: the positions above 10000 are 0; open, as expected, the guarded stores are not read without a
// lemma
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    if i >= 0 && i <= 10000 {
      a := a[i := 10];
    } else {
      a := a[i := 0];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == 10;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₂: array<int, int>, a₁₀: array<int, int>, K₇: Trace<int>,
//          A₈: Trace<array<int, int>>, I₉: Trace<int>, n₁₃: int, K₁₅: Trace<int>,
//          I₁₆: Trace<int> ::
//     K₇ == counter(0, 1, 100000)
//       && a₁₀ == current(A₈)
//       && A₈
//         == trace(a₂, for ⌊K₇⌋, ⌊I₉⌋
//                      do a₃, k₆, i₄ ::
//                        case k₆ <= 10000 => a₃[k₆ := 10]
//                        case 10000 < k₆ => a₃[k₆ := 0])
//       && I₉ == counter(0, 1, 100000)
//       && K₁₅ == counter(0, 1, n₁₃)
//       && I₁₆ == counter(0, 1, n₁₃)
//       && invs(for ⌊K₁₅⌋, ⌊I₁₆⌋ check k₁₄, i₁₂ :: a₁₀[k₁₄] == 10)
//       && 0 <= n₁₃ < 100000
//       ==> a₁₀[n₁₃] == 10
