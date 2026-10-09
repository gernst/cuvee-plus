// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_minInArray_ground-1.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_minInArray_ground-1.yml (expected: unsafe), translated from the C program by hand:
// the minimum of 0 and the elements is computed, and each element is checked to be above it, which fails for
// the minimal element
//
// findings: unsafe: the minimal element is not above the minimum; open, as expected

method main() {
  var i: int;
  var j: int;
  var x: int;
  var v: int;
  var min: int;
  var a: array<int, int>;
  min := 0;
  j := 0;
  while j < 100000 {
    havoc v;
    a := a[j := v];
    j := j + 1;
  }
  i := 0;
  while i < 100000 {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a[x] > min;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall V?₁₁: seq<int>, min₂₉: int, Min₂₇: Trace<int>, n₃₂: int,
//          K₃₄: Trace<int>, X₃₅: Trace<int> ::
//     min₂₉ == current(Min₂₇)
//       && Min₂₇ == mins(0, V?₁₁)
//       && K₃₄ == counter(0, 1, n₃₂)
//       && X₃₅ == counter(0, 1, n₃₂)
//       && invs(for ⌊K₃₄⌋, ⌊X₃₅⌋ check k₃₃, x₃₁ :: min₂₉ < earlier(k₃₃, V?₁₁))
//       && 0 <= n₃₂ < 100000
//       ==> min₂₉ < earlier(n₃₂, V?₁₁)
