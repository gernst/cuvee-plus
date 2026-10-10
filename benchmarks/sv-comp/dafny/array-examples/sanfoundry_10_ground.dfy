// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/sanfoundry_10_ground.dfy
// SV-COMP array-examples/sanfoundry_10_ground.yml (expected: safe), translated from the C program by hand:
// the first position pos of an element is searched, the elements after it are shifted down by one, and the
// elements before pos are checked to differ from it
//
// findings: open: the search loop leaves at the first occurrence of the element, whose position pos is a trace that
// keeps its value, and the elements before pos are then shifted; the goal needs the iteration constraint that the
// flag is 0 before the exit, i.e., that the element does not occur before pos, and reads past the shift at
// positions below pos; no lemmas tried
// note: the concrete loop bounds are symbolic, arbitrary positive values: n for 100000

method main() {
  var i: int;
  var x: int;
  var v: int;
  var n: int;
  var pos: int;
  var element: int;
  var found: int;
  var vectorx: array<int, int>;
  n := *;
  assume 0 < n;
  element := *;
  found := 0;
  i := 0;
  while i < n {
    v := *;
    vectorx := vectorx[i := v];
    i := i + 1;
  }
  i := 0;
  while i < n && found == 0 {
    if vectorx[i] == element {
      found := 1;
      pos := i;
    }
    i := i + 1;
  }
  if found != 0 {
    i := pos;
    while i < n - 1 {
      vectorx := vectorx[i := vectorx[i + 1]];
      i := i + 1;
    }
  }
  if found != 0 {
    x := 0;
    while x < pos {
      assert vectorx[x] != element;
      x := x + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall pos₅: int, vectorx₈: array<int, int>, element₉: int, V?₁₄: seq<int>,
//          found₃₄: int, pos₃₅: int, n₂₈: int, K₃₀: Trace<int>,
//          Found₃₁: Trace<int>, Pos₃₂: Trace<int>, I₃₃: Trace<int>, n₃₉: int,
//          n₄₇: int, K₄₉: Trace<int>, X₅₀: Trace<int> ::
//     !(K₃₀ == counter(0, 1, n₂₈)
//         && found₃₄ == current(Found₃₁)
//         && pos₃₅ == current(Pos₃₂)
//         && Found₃₁
//           == trace(0, for ⌊K₃₀⌋, ⌊I₃₃⌋
//                       do found₂₅, k₂₉, i₂₇ ::
//                         case earlier(k₂₉, V?₁₄) == element₉ => 1
//                         case earlier(k₂₉, V?₁₄) != element₉ => 0)
//         && Pos₃₂
//           == trace(pos₅, for ⌊K₃₀⌋, ⌊I₃₃⌋
//                          do pos₂₆, k₂₉, i₂₇ ::
//                            case earlier(k₂₉, V?₁₄) == element₉ => k₂₉
//                            case earlier(k₂₉, V?₁₄) != element₉ => pos₂₆)
//         && I₃₃ == counter(0, 1, n₂₈)
//         && n₂₈ < 100001
//         && invs(for ⌊K₃₀⌋, ⌊Found₃₁⌋, ⌊I₃₃⌋
//                 check k₂₉, found₂₅, i₂₇ ::
//                   found₂₅ == 0)
//         && 0 <= n₂₈
//         && (n₃₉ == 0 || pos₃₅ < 99999 && n₃₉ + pos₃₅ < 100000)
//         && 0 <= n₃₉
//         && 99999 <= n₃₉ + pos₃₅
//         && found₃₄ != 0
//         && K₄₉ == counter(0, 1, n₄₇)
//         && X₅₀ == counter(0, 1, n₄₇)
//         && invs(for ⌊K₄₉⌋, ⌊X₅₀⌋
//                 check k₄₈, x₄₆ ::
//                   (if k₄₈ < 100000 then earlier(k₄₈, V?₁₄) else vectorx₈[k₄₈])
//                     != element₉)
//         && 0 <= n₄₇ < pos₃₅
//         && (if n₄₇ < 100000 then earlier(n₄₇, V?₁₄) else vectorx₈[n₄₇])
//           == element₉)
