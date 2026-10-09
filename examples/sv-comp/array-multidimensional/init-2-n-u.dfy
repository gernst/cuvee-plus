// ./Cuvee.sh -teq -simplify examples/sv-comp/array-multidimensional/init-2-n-u.dfy
// SV-COMP array-multidimensional/init-2-n-u.yml (expected: safe), translated from the C program by
// hand: a two-dimensional array, an array of rows, is set to C by nested loops, and checked by nested loops
//
// findings: the representative of the folder, all of whose 20 tasks are nested loops over arrays of rows (init,
// copy, add, diff, min, max, rev, transpose in 2 to 4 dimensions); open: -teq summarizes the inner loop per
// iteration of the outer one by iteration constraints over sequences of traces (A?, J?, K?), e.g. that the inner
// trace is a trace over the inner counter, whose length 1500 is stated only by sums(0, maps(... 1)) and the exit
// 1500 <= j; the outer trace takes the inner results A₁₈, and teq.dfy has no rule that composes the two (see
// TODO.md, nested loops); a lemma would have to combine the iteration constraints of the outer loop into a closed
// form of the outer trace, which is the composition of nested loops listed among the further ideas of the summary
// note: the concrete loop bounds are symbolic, arbitrary positive values: m for 1000, n for 1500

method main() {
  var i: int;
  var j: int;
  var m: int;
  var n: int;
  var C: int;
  var A: array<int, array<int, int>>;
  m := *;
  assume 0 < m;
  n := *;
  assume 0 < n;
  C := *;
  i := 0;
  while i < m {
    j := 0;
    while j < n {
      A := A[i := A[i][j := C]];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  while i < m {
    j := 0;
    while j < n {
      assert A[i][j] == C;
      j := j + 1;
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall A₆: array<int, array<int, int>>, C₇: int,
//          A₃₃: array<int, array<int, int>>, K₂₈: Trace<int>,
//          A₃₀: Trace<array<int, array<int, int>>>, I₃₁: Trace<int>,
//          A?₂₀: seq<array<int, array<int, int>>>, J?₂₁: seq<int>, N?₂₂: seq<int>,
//          K?₂₃: seq<Trace<int>>, A?₂₄: seq<Trace<array<int, array<int, int>>>>,
//          J?₂₅: seq<Trace<int>>, n₅₆: int, K₅₈: Trace<int>, I₆₀: Trace<int>,
//          J?₅₂: seq<int>, N?₅₃: seq<int>, K?₅₄: seq<Trace<int>>,
//          J?₅₅: seq<Trace<int>>, n₆₄: int, K₆₆: Trace<int>, J₆₇: Trace<int> ::
//     K₂₈ == counter(0, 1, 1000)
//       && A₃₃ == current(A₃₀)
//       && A₃₀ == trace(A₆, for ⌊K₂₈⌋, A?₂₀ do A₉, k₂₇, A₁₈ :: A₁₈)
//       && I₃₁ == counter(0, 1, 1000)
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, N?₂₂, K?₂₃
//               check k₂₇, i₁₀, n₁₃, K₁₅ ::
//                 K₁₅ == counter(0, 1, n₁₃))
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, A?₂₀, A?₂₄
//               check k₂₇, i₁₀, A₁₈, A₁₆ ::
//                 A₁₈ == current(A₁₆))
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, J?₂₁, J?₂₅
//               check k₂₇, i₁₀, j₁₉, J₁₇ ::
//                 j₁₉ == current(J₁₇))
//       && invs(for ⌊K₂₈⌋, ⌊A₃₀⌋, ⌊I₃₁⌋, A?₂₄, J?₂₅
//               check k₂₇, A₉, i₁₀, A₁₆, J₁₇ ::
//                 A₁₆
//                   == trace(A₉, for ⌊J₁₇⌋
//                                do A₁₁, j₁₂ ::
//                                  A₁₁[k₂₇ := A₁₁[k₂₇][j₁₂ := C₇]]))
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, K?₂₃, J?₂₅
//               check k₂₇, i₁₀, K₁₅, J₁₇ ::
//                 J₁₇ == sums(0, maps(for ⌊K₁₅⌋ yield k₁₄ :: 1)))
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, J?₂₅
//               check k₂₇, i₁₀, J₁₇ ::
//                 invs(for ⌊J₁₇⌋ check j₁₂ :: j₁₂ < 1500))
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, N?₂₂ check k₂₇, i₁₀, n₁₃ :: 0 <= n₁₃)
//       && invs(for ⌊K₂₈⌋, ⌊I₃₁⌋, J?₂₁ check k₂₇, i₁₀, j₁₉ :: 1500 <= j₁₉)
//       && K₅₈ == counter(0, 1, n₅₆)
//       && I₆₀ == counter(0, 1, n₅₆)
//       && invs(for ⌊K₅₈⌋, ⌊I₆₀⌋, N?₅₃, K?₅₄
//               check k₅₇, i₄₅, n₄₇, K₄₉ ::
//                 K₄₉ == counter(0, 1, n₄₇))
//       && invs(for ⌊K₅₈⌋, ⌊I₆₀⌋, J?₅₂, J?₅₅
//               check k₅₇, i₄₅, j₅₁, J₅₀ ::
//                 j₅₁ == current(J₅₀))
//       && invs(for ⌊K₅₈⌋, ⌊I₆₀⌋, K?₅₄, J?₅₅
//               check k₅₇, i₄₅, K₄₉, J₅₀ ::
//                 J₅₀ == sums(0, maps(for ⌊K₄₉⌋ yield k₄₈ :: 1)))
//       && invs(for ⌊K₅₈⌋, ⌊I₆₀⌋, J?₅₅
//               check k₅₇, i₄₅, J₅₀ ::
//                 invs(for ⌊J₅₀⌋ check j₄₆ :: j₄₆ < 1500))
//       && invs(for ⌊K₅₈⌋, ⌊I₆₀⌋, J?₅₅
//               check k₅₇, i₄₅, J₅₀ ::
//                 invs(for ⌊J₅₀⌋ check j₄₆ :: A₃₃[k₅₇][j₄₆] == C₇))
//       && invs(for ⌊K₅₈⌋, ⌊I₆₀⌋, N?₅₃ check k₅₇, i₄₅, n₄₇ :: 0 <= n₄₇)
//       && invs(for ⌊K₅₈⌋, ⌊I₆₀⌋, J?₅₂ check k₅₇, i₄₅, j₅₁ :: 1500 <= j₅₁)
//       && 0 <= n₅₆ < 1000
//       && K₆₆ == counter(0, 1, n₆₄)
//       && J₆₇ == counter(0, 1, n₆₄)
//       && invs(for ⌊K₆₆⌋, ⌊J₆₇⌋ check k₆₅, j₆₃ :: A₃₃[n₅₆][k₆₅] == C₇)
//       && 0 <= n₆₄ < 1500
//       ==> A₃₃[n₅₆][n₆₄] == C₇
