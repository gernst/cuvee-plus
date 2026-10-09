// ./Cuvee.sh -teq -simplify examples/sv-comp/array-programs/copysome1-2.dfy
// SV-COMP array-programs/copysome1-2.yml (expected: unsafe), translated from the C program by
// hand: the unsafe variant of copysome1-1, where z is 150001 in the check, such that the position 150000, which is
// not copied, is compared
//
// findings: unsafe, not closed with the lemmas of copysome1-1, as expected: the position 150000, which is not
// copied, is compared
// note: 2 of its lemmas are part of teq.dfy now and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 200000

method main() {
  var N: int;
  var a1: array<int, int>;
  var a2: array<int, int>;
  var i: int;
  var z: int;
  var x: int;
  var tmp: int;
  assume 0 < N;
  z := 150000;
  i := 0;
  while i < N {
    tmp := *;
    a1 := a1[i := tmp];
    tmp := *;
    a2 := a2[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i != z {
      a2 := a2[i := a1[i]];
    }
    i := i + 1;
  }
  z := 150001;
  x := 0;
  while x < N {
    if x != z {
      assert a1[x] == a2[x];
    }
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
//                 earlier(k₃₉, Tmp?₁₃)
//                   == (if k₃₉ != 150000
//                       then earlier(k₃₉, Tmp?₁₃)
//                       else earlier(150000, Tmp?₁₄))
//                   || k₃₉ == 150001)
//       && 0 <= n₃₈ < 200000
//       && n₃₈ != 150001
//       ==> earlier(n₃₈, Tmp?₁₃)
//         == (if n₃₈ != 150000
//             then earlier(n₃₈, Tmp?₁₃)
//             else earlier(150000, Tmp?₁₄))
