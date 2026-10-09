// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-simple/nested_2.dfy
// SV-COMP loop-simple/nested_2.yml (expected: safe), translated from the C program by hand: two
// nested loops count a and b to 6, and both are 6 at the end
//
// findings: the inner loop is summarized per iteration of the outer one, by sequences of values and traces with
// iteration constraints that relate them (b == current(B), B == sums(0, ...), the inner exit 6 <= b, the inner
// constraint b < 6 before); b == 6 at the end needs these constraints combined in each iteration and the last value
// of the outer trace, which takes the values of the sequence, i.e., the composition of the loops, as in nested-1;
// no lemma is added
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 6

method main() {
  var N: int;
  var a: int;
  var b: int;
  assume 0 < N;
  a := N;
  b := N;
  a := 0;
  while a < N {
    b := 0;
    while b < N {
      b := b + 1;
    }
    a := a + 1;
  }
  assert a == N && b == N;
}

// remaining goals of -teq -simplify:
// goal
//   forall b₂₀: int, K₁₇: Trace<int>, B₁₈: Trace<int>, A₁₉: Trace<int>,
//          B?₁₁: seq<int>, N?₁₂: seq<int>, K?₁₃: seq<Trace<int>>,
//          B?₁₄: seq<Trace<int>> ::
//     K₁₇ == counter(0, 1, 6)
//       && b₂₀ == current(B₁₈)
//       && B₁₈ == trace(6, for ⌊K₁₇⌋, B?₁₁ do b₃, k₁₆, b₁₀ :: b₁₀)
//       && A₁₉ == counter(0, 1, 6)
//       && invs(for ⌊K₁₇⌋, ⌊A₁₉⌋, N?₁₂, K?₁₃
//               check k₁₆, a₄, n₆, K₈ ::
//                 K₈ == counter(0, 1, n₆))
//       && invs(for ⌊K₁₇⌋, ⌊A₁₉⌋, B?₁₁, B?₁₄
//               check k₁₆, a₄, b₁₀, B₉ ::
//                 b₁₀ == current(B₉))
//       && invs(for ⌊K₁₇⌋, ⌊A₁₉⌋, K?₁₃, B?₁₄
//               check k₁₆, a₄, K₈, B₉ ::
//                 B₉ == sums(0, maps(for ⌊K₈⌋ yield k₇ :: 1)))
//       && invs(for ⌊K₁₇⌋, ⌊A₁₉⌋, B?₁₄
//               check k₁₆, a₄, B₉ ::
//                 invs(for ⌊B₉⌋ check b₅ :: b₅ < 6))
//       && invs(for ⌊K₁₇⌋, ⌊A₁₉⌋, N?₁₂ check k₁₆, a₄, n₆ :: 0 <= n₆)
//       && invs(for ⌊K₁₇⌋, ⌊A₁₉⌋, B?₁₁ check k₁₆, a₄, b₁₀ :: 6 <= b₁₀)
//       ==> b₂₀ == 6
