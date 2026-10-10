// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-programs/partial_mod_count_limited_1.dfy
// SV-COMP array-programs/partial_mod_count_limited_1.yml (expected: safe), translated from the C program by hand:
// a[i] = i + 1, overwritten by i % R = 0 with R = 1 while the count k of zeros is below lim < N, and the count
// j of zeros is checked to stay below N (unsigned R is int)
//
// findings: the stores depend on a second trace, the count k of zeros, which is below lim; open: the stored value
// depends on k < lim, a condition on a trace that is not a counter, such that the count of zeros is that of a
// prefix of length lim, which needs the trace k as a function of the iterations; no lemmas tried
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() {
  var N: int;
  var i: int;
  var j: int;
  var k: int;
  var R: int;
  var lim: int;
  var a: array<int, int>;
  assume 0 < N;
  j := 0;
  k := 0;
  lim := *;
  R := 1;
  assume 0 < lim && lim < N / R;
  i := 0;
  while i < N {
    a := a[i := i + 1];
    if k < lim {
      a := a[i := i % R];
    }
    if a[i] == 0 {
      k := k + 1;
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] == 0 {
      j := j + 1;
    }
    assert j < N / R;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall a₇: array<int, int>, lim₈: int, a₁₈: array<int, int>, K₁₄: Trace<int>,
//          A₁₅: Trace<array<int, int>>, K₁₆: Trace<int>, I₁₇: Trace<int>,
//          j₂₈: int, n₂₃: int, K₂₅: Trace<int>, J₂₆: Trace<int>,
//          I₂₇: Trace<int> ::
//     0 < lim₈ < 1000000
//       && K₁₄ == counter(0, 1, 1000000)
//       && a₁₈ == current(A₁₅)
//       && A₁₅
//         == trace(a₇, for ⌊K₁₄⌋, ⌊K₁₆⌋, ⌊I₁₇⌋
//                      do a₉, k₁₃, k₁₀, i₁₁ ::
//                        case k₁₀ < lim₈ => a₉[k₁₃ := 0]
//                        case lim₈ <= k₁₀ => a₉[k₁₃ := k₁₃ + 1])
//       && K₁₆
//         == trace(0, for ⌊K₁₄⌋, ⌊I₁₇⌋
//                     do k₁₀, k₁₃, i₁₁ ::
//                       case k₁₀ < lim₈ => k₁₀ + 1 case lim₈ <= k₁₀ => k₁₀)
//       && I₁₇ == counter(0, 1, 1000000)
//       && K₂₅ == counter(0, 1, n₂₃)
//       && j₂₈ == count(0, selects(a₁₈, ⌊I₂₇⌋))
//       && J₂₆ == counts(0, 0, selects(a₁₈, ⌊I₂₇⌋))
//       && I₂₇ == counter(0, 1, n₂₃)
//       && invs(for ⌊K₂₅⌋, ⌊J₂₆⌋, ⌊I₂₇⌋
//               check k₂₄, j₂₁, i₂₂ ::
//                 a₁₈[k₂₄] == 0 && j₂₁ < 999999 || a₁₈[k₂₄] != 0 && j₂₁ < 1000000)
//       && 0 <= n₂₃ < 1000000
//       ==> (a₁₈[n₂₃] == 0 ==> j₂₈ < 999999) && (a₁₈[n₂₃] != 0 ==> j₂₈ < 1000000)
