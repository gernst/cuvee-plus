// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/s1lif.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/s1lif.yml (expected: safe), translated from the C program by hand: a is set
// to 1, incremented where it is 1, and summed up, which gives 2 N (s2lif to s5lif are variants)
//
// findings: open: as s12if, the update of a[k] by a case split on a[k] itself, which a lemma would need to read at
// the initial value, whose higher-order patterns do not take a read as argument (see TODO.md); the variants s2lif
// to s5lif are not translated

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  havoc N;
  assume 0 < N <= 536870911;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] == 1 {
      a := a[i := a[i] + 1];
    } else {
      a := a[i := a[i] - 1];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  assert sum == 2 * N;
}

// remaining goals of -teq -simplify:
// goal
//   forall a₄: array<int, int>, N₅: int, a₁₃: array<int, int>,
//          A₁₁: Trace<array<int, int>>, I₁₂: Trace<int>, a₂₂: array<int, int>,
//          K₁₉: Trace<int>, A₂₀: Trace<array<int, int>>, I₂₁: Trace<int>,
//          sum₃₁: int, I₃₀: Trace<int> ::
//     0 < N₅ <= 536870911
//       && a₁₃ == current(A₁₁)
//       && A₁₁ == stores(a₄, ⌊I₁₂⌋, ⌊consts(N₅, 1)⌋)
//       && I₁₂ == counter(0, 1, N₅)
//       && K₁₉ == counter(0, 1, N₅)
//       && a₂₂ == current(A₂₀)
//       && A₂₀
//         == trace(a₁₃, for ⌊K₁₉⌋, ⌊I₂₁⌋
//                       do a₁₅, k₁₈, i₁₆ ::
//                         case a₁₅[k₁₈] == 1 => a₁₅[k₁₈ := 2]
//                         case a₁₅[k₁₈] != 1 => a₁₅[k₁₈ := a₁₅[k₁₈] + -1])
//       && I₂₁ == counter(0, 1, N₅)
//       && sum₃₁ == sum(selects(a₂₂, ⌊I₃₀⌋))
//       && I₃₀ == counter(0, 1, N₅)
//       ==> sum₃₁ == 2 * N₅
