// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_copy1_ground-2.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_copy1_ground-2.yml (expected: unsafe), translated from the C
// program by hand: the unsafe variant of standard_copy1_ground-1: a2 is filled with arbitrary values as well, and
// the copy assigns a1 to itself, such that a2 is not a copy
//
// findings: unsafe, not closed, as expected: a2 is arbitrary, and the goal compares an arbitrary element of it with
// a1

method main() {
  var a1: array<int, int>;
  var a2: array<int, int>;
  var a: int;
  var i: int;
  var x: int;
  var tmp: int;
  a := 0;
  while a < 100000 {
    tmp := *;
    a1 := a1[a := tmp];
    tmp := *;
    a2 := a2[a := tmp];
    a := a + 1;
  }
  i := 0;
  while i < 100000 {
    a1 := a1[i := a1[i]];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a1[x] == a2[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall Tmp?₁₃: seq<int>, Tmp?₁₄: seq<int>, n₃₈: int, K₄₀: Trace<int>,
//          X₄₁: Trace<int> ::
//     K₄₀ == counter(0, 1, n₃₈)
//       && X₄₁ == counter(0, 1, n₃₈)
//       && invs(for ⌊K₄₀⌋, ⌊X₄₁⌋
//               check k₃₉, x₃₇ ::
//                 earlier(k₃₉, Tmp?₁₃) == earlier(k₃₉, Tmp?₁₄))
//       && 0 <= n₃₈ < 100000
//       ==> earlier(n₃₈, Tmp?₁₃) == earlier(n₃₈, Tmp?₁₄)
