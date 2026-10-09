// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/s12if.dfy
// SV-COMP array-fpi/s12if.yml (expected: safe), translated from the C program by hand: a is set
// to 1, incremented where it is 1, and its elements are added to sum if they are 2, which gives 2 N (s22if to s52if
// are variants)
//
// findings: open: the second loop updates a[k] by a case split on a[k] itself, which reads the initial value, as no
// earlier iteration wrote position k; a lemma stating that does not match, since its higher-order patterns C(a[k])
// and F(a[k]) take a read as their argument, not a bound variable (see TODO.md, higher-order patterns); the
// variants s22if to s52if are not translated

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// an update at the position k of the iteration k that reads the array at k reads its initial value, which no earlier
// iteration has overwritten (with a further dependency ys)
lemma {:rw} {:teq} trace_1(a0: array<int, int>, n: int, ys: seq<int>, C: (int) -> bool, F: (int) -> int,
                           G: (int) -> int)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: case C(a[k]) => a[k := F(a[k])] case !C(a[k]) => a[k := G(a[k])])
      == trace(a0, for ⌊counter(0, 1, n)⌋, ys do a, k, y :: a[k := if C(a0[k]) then F(a0[k]) else G(a0[k])])

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  N := *;
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
    if a[i] == 2 {
      sum := sum + a[i];
    } else {
      sum := sum * a[i];
    }
    i := i + 1;
  }
  assert sum == 2 * N;
}

// remaining goals of -teq -simplify:
// goal
//   forall a₄: array<int, int>, N₅: int, a₁₃: array<int, int>,
//          A₁₁: Trace<array<int, int>>, I₁₂: Trace<int>, a₂₂: array<int, int>,
//          K₁₉: Trace<int>, A₂₀: Trace<array<int, int>>, I₂₁: Trace<int>,
//          sum₃₁: int, K₂₈: Trace<int>, Sum₂₉: Trace<int>, I₃₀: Trace<int> ::
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
//       && K₂₈ == counter(0, 1, N₅)
//       && sum₃₁ == current(Sum₂₉)
//       && Sum₂₉
//         == trace(0, for ⌊K₂₈⌋, ⌊I₃₀⌋
//                     do sum₂₄, k₂₇, i₂₅ ::
//                       case a₂₂[k₂₇] == 2 => sum₂₄ + 2
//                       case a₂₂[k₂₇] != 2 => a₂₂[k₂₇] * sum₂₄)
//       && I₃₀ == counter(0, 1, N₅)
//       ==> sum₃₁ == 2 * N₅
