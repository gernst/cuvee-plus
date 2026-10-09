// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-new/nested-1.dfy
// SV-COMP ReachSafety-Loops/loop-new/nested-1.yml (expected: safe), translated from the C program by hand: k counts
// the iterations of two nested loops over n and m, both at least 10, which are at least 100
//
// findings: the inner loop is summarized by sequences of traces, whose current values are sums of 1 over counters
// of m iterations, and the outer loop takes the value of the inner one; the goal needs the composition of the two,
// k == n * m, i.e., an acceleration of a trace that sums the lengths of the inner traces, which teq.dfy does not
// have; no lemma is added

method main() {
  var n: int;
  var m: int;
  var k: int;
  var i: int;
  var j: int;
  havoc n;
  havoc m;
  assume 10 <= n <= 10000;
  assume 10 <= m <= 10000;
  k := 0;
  i := 0;
  while i < n {
    j := 0;
    while j < m {
      k := k + 1;
      j := j + 1;
    }
    i := i + 1;
  }
  assert k >= 100;
}

// remaining goals of -teq -simplify:
// goal
//   forall n₆: int, m₇: int, k₃₃: int, K₂₈: Trace<int>, K₃₀: Trace<int>,
//          I₃₁: Trace<int>, K?₂₀: seq<int>, J?₂₁: seq<int>, N?₂₂: seq<int>,
//          K?₂₃: seq<Trace<int>>, K?₂₄: seq<Trace<int>>, J?₂₅: seq<Trace<int>> ::
//     10 <= n₆ <= 10000
//       && 10 <= m₇ <= 10000
//       && K₂₈ == counter(0, 1, n₆)
//       && k₃₃ == current(K₃₀)
//       && K₃₀ == trace(0, for ⌊K₂₈⌋, K?₂₀ do k₉, k₂₇, k₁₈ :: k₁₈)
//       && I₃₁ == counter(0, 1, n₆)
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, N?₂₂, K?₂₃
//               check k₂₇, i₁₀, n₁₃, K₁₅ ::
//                 K₁₅ == counter(0, 1, n₁₃))
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, K?₂₀, K?₂₄
//               check k₂₇, i₁₀, k₁₈, K₁₆ ::
//                 k₁₈ == current(K₁₆))
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, J?₂₁, J?₂₅
//               check k₂₇, i₁₀, j₁₉, J₁₇ ::
//                 j₁₉ == current(J₁₇))
//       && invs(for ⌊K₂₈⌋, ⌊K₃₀⌋, ⌊I₃₁⌋, K?₂₃, K?₂₄
//               check k₂₇, k₉, i₁₀, K₁₅, K₁₆ ::
//                 K₁₆ == sums(k₉, maps(for ⌊K₁₅⌋ yield k₁₄ :: 1)))
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, K?₂₃, J?₂₅
//               check k₂₇, i₁₀, K₁₅, J₁₇ ::
//                 J₁₇ == sums(0, maps(for ⌊K₁₅⌋ yield k₁₄ :: 1)))
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, J?₂₅
//               check k₂₇, i₁₀, J₁₇ ::
//                 invs(for ⌊J₁₇⌋ check j₁₂ :: j₁₂ < m₇))
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, N?₂₂ check k₂₇, i₁₀, n₁₃ :: 0 <= n₁₃)
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, J?₂₁ check k₂₇, i₁₀, j₁₉ :: m₇ <= j₁₉)
//       ==> 100 <= k₃₃
