// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-acceleration/nested_1-2.dfy
// SV-COMP loop-acceleration/nested_1-2.yml (expected: unsafe), translated from the C program by
// hand: the unsafe variant of nested_1-1, which asserts that the final x, which is odd, is even
//
// findings: unsafe, not closed, as expected
// note: the concrete loop bounds are symbolic, arbitrary positive values: M for 268435455, L for 10

method main() {
  var M: int;
  var L: int;
  var x: int;
  var y: int;
  assume 0 < M;
  assume 0 < L;
  x := 0;
  y := 0;
  while x < M {
    y := 0;
    while y < L {
      y := y + 1;
    }
    x := x + 1;
  }
  assert rem(x, 2) == 0;
}

// remaining goals of -teq -simplify:
// goal
//   forall K₁₇: Trace<int>, X₁₉: Trace<int>, Y?₁₁: seq<int>, N?₁₂: seq<int>,
//          K?₁₃: seq<Trace<int>>, Y?₁₄: seq<Trace<int>> ::
//     !(K₁₇ == counter(0, 1, 268435455)
//         && X₁₉ == counter(0, 1, 268435455)
//         && invs(for ⌊K₁₇⌋, ⌊X₁₉⌋, N?₁₂, K?₁₃
//                 check k₁₆, x₄, n₆, K₈ ::
//                   K₈ == counter(0, 1, n₆))
//         && invs(for ⌊K₁₇⌋, ⌊X₁₉⌋, Y?₁₁, Y?₁₄
//                 check k₁₆, x₄, y₁₀, Y₉ ::
//                   y₁₀ == current(Y₉))
//         && invs(for ⌊K₁₇⌋, ⌊X₁₉⌋, K?₁₃, Y?₁₄
//                 check k₁₆, x₄, K₈, Y₉ ::
//                   Y₉ == sums(0, maps(for ⌊K₈⌋ yield k₇ :: 1)))
//         && invs(for ⌊K₁₇⌋, ⌊X₁₉⌋, Y?₁₄
//                 check k₁₆, x₄, Y₉ ::
//                   invs(for ⌊Y₉⌋ check y₅ :: y₅ < 10))
//         && invs(for ⌊K₁₇⌋, ⌊X₁₉⌋, N?₁₂ check k₁₆, x₄, n₆ :: 0 <= n₆)
//         && invs(for ⌊K₁₇⌋, ⌊X₁₉⌋, Y?₁₁ check k₁₆, x₄, y₁₀ :: 10 <= y₁₀))
