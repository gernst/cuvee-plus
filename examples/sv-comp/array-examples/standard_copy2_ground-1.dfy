// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_copy2_ground-1.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_copy2_ground-1.yml (expected: unsafe), translated from the C program by hand:
// a1 and a2 are arbitrary, a1 is copied into a3, and a3 is then overwritten by a copy of a2, which is checked
// to agree with a1
//
// findings: unsafe: a3 ends as a copy of a2, not a1; open, as expected (the -1 variants of standard_copy3 to _copy9
// are similar)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var x: int;
  var v: int;
  var a1: array<int, int>;
  var a2: array<int, int>;
  var a3: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    v := *;
    a1 := a1[i := v];
    v := *;
    a2 := a2[i := v];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a3 := a3[i := a1[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a3 := a3[i := a2[i]];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert a1[x] == a3[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall V?₁₃: seq<int>, V?₁₄: seq<int>, n₄₇: int, K₄₉: Trace<int>,
//          X₅₀: Trace<int> ::
//     K₄₉ == counter(0, 1, n₄₇)
//       && X₅₀ == counter(0, 1, n₄₇)
//       && invs(for ⌊K₄₉⌋, ⌊X₅₀⌋
//               check k₄₈, x₄₆ ::
//                 earlier(k₄₈, V?₁₃) == earlier(k₄₈, V?₁₄))
//       && 0 <= n₄₇ < 100000
//       ==> earlier(n₄₇, V?₁₃) == earlier(n₄₇, V?₁₄)
