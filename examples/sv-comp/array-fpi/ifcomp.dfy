// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-fpi/ifcomp.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/ifcomp.yml (expected: safe), translated from the C program by hand: three
// arrays by recurrences, whose first elements are set in the first iteration: a the multiples of 6, b their partial
// sums plus 1, c the partial sums of b, which are the cubes i * i * i
//
// findings: three recurrences whose first elements are set in the first iteration under the guard i == 0; the
// counters have the cases 1 and i + 1, which a lemma joins (see copysome1-1), after which the updates read the
// predecessor at k - 1; the lemma for such recurrences, with the closed form c plus the sum of G over the
// positions, does not match, since a pattern with a sum over a bound variable of a combinator, a[k - 1], is not
// matched, even against itself (see TODO.md), unlike the recurrences of eqn1, whose index is a dependency; the
// lemmas are kept
// note: 1 of its lemmas are part of teq.dfy now and are removed here

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function sum(values: seq<int>): int

// an array filled by a recurrence whose first element c is set in the first iteration, under the guard i == 0, and
// each further element from its predecessor plus G(i), has the closed form c plus the sum of G over 1, ..., j, stated
// over the iterations as G(k + 1), and keeps the positions from n on; G is applied to the position k, since a term
// k - 1 as its argument would be no pattern; the position is the iteration k, which the simplifier substitutes for
// the index i once its trace is a counter
lemma {:rw} {:free} {:teq} forall a0: array<int, int>, n: int, j: int, c: int, hs: seq<int>, G: (int) -> int ::
  current(trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h ::
                  case k == 0 => a[0 := c] case k != 0 => a[k := a[k - 1] + G(k)]))[j]
    == if 0 <= j < n then c + sum(maps(for ⌊counter(0, 1, j)⌋ yield k :: G(k + 1))) else a0[j]

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  var i: int;
  N := *;
  assume 0 < N <= 536870911;
  i := 0;
  while i < N {
    if i == 0 {
      a := a[0 := 6];
    } else {
      a := a[i := a[i - 1] + 6];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      b := b[0 := 1];
    } else {
      b := b[i := b[i - 1] + a[i - 1]];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      c := c[0 := 0];
    } else {
      c := c[i := c[i - 1] + b[i - 1]];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert c[i] == i * i * i;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// goal
//   forall a₂: array<int, int>, b₃: array<int, int>, c₄: array<int, int>, N₆: int,
//          a₁₄: array<int, int>, K₁₁: Trace<int>, A₁₂: Trace<array<int, int>>,
//          I₁₃: Trace<int>, b₂₃: array<int, int>, K₂₀: Trace<int>,
//          B₂₁: Trace<array<int, int>>, I₂₂: Trace<int>, c₃₂: array<int, int>,
//          K₂₉: Trace<int>, C₃₀: Trace<array<int, int>>, I₃₁: Trace<int>,
//          n₃₅: int, K₃₇: Trace<int>, I₃₈: Trace<int> ::
//     N₆ <= 536870911
//       && K₁₁ == counter(0, 1, N₆)
//       && a₁₄ == current(A₁₂)
//       && A₁₂
//         == trace(a₂, for ⌊K₁₁⌋, ⌊I₁₃⌋
//                      do a₇, k₁₀, i₈ ::
//                        case k₁₀ == 0 => a₇[0 := 6]
//                        case k₁₀ != 0 => a₇[k₁₀ := a₇[k₁₀ + -1] + 6])
//       && I₁₃ == counter(0, 1, N₆)
//       && K₂₀ == counter(0, 1, N₆)
//       && b₂₃ == current(B₂₁)
//       && B₂₁
//         == trace(b₃, for ⌊K₂₀⌋, ⌊I₂₂⌋
//                      do b₁₆, k₁₉, i₁₇ ::
//                        case k₁₉ == 0 => b₁₆[0 := 1]
//                        case k₁₉ != 0 => b₁₆[
//                          k₁₉ :=
//                          a₁₄[k₁₉ + -1] + b₁₆[k₁₉ + -1]])
//       && I₂₂ == counter(0, 1, N₆)
//       && K₂₉ == counter(0, 1, N₆)
//       && c₃₂ == current(C₃₀)
//       && C₃₀
//         == trace(c₄, for ⌊K₂₉⌋, ⌊I₃₁⌋
//                      do c₂₅, k₂₈, i₂₆ ::
//                        case k₂₈ == 0 => c₂₅[0 := 0]
//                        case k₂₈ != 0 => c₂₅[
//                          k₂₈ :=
//                          b₂₃[k₂₈ + -1] + c₂₅[k₂₈ + -1]])
//       && I₃₁ == counter(0, 1, N₆)
//       && K₃₇ == counter(0, 1, n₃₅)
//       && I₃₈ == counter(0, 1, n₃₅)
//       && invs(for ⌊K₃₇⌋, ⌊I₃₈⌋ check k₃₆, i₃₄ :: c₃₂[k₃₆] == k₃₆ * k₃₆ * k₃₆)
//       && 0 <= n₃₅ < N₆
//       ==> c₃₂[n₃₅] == n₃₅ * n₃₅ * n₃₅
