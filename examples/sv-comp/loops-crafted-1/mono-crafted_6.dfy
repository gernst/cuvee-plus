// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_6.dfy
// SV-COMP loops-crafted-1/mono-crafted_6.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x counts to 1000000, by 1 below 750000 and by 2 above, and x == 1000000 is checked
//
// findings: open: x counts by 1 below 750000 and by 2 above, a two-phase counter whose exit is reached exactly at
// 1000000, which needs the number of iterations of the second phase, (1000000 - 750000) / 2; the lemma of
// mono-crafted_8 states a phase that changes another value, not the loop variable; no lemmas tried
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var x: int, y: int, z: int;
    x := 0;
    y := 500000;
    z := 0;
    x := 0;
    while x < N {
      if x < 500000 {
        x := x + 1;
      } else {
        if x < 750000 {
          x := x + 1;
        } else {
          x := x + 2;
        }
        y := y + 1;
      }
    }
    assert x == N;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall x₁₁: int, n₆: int, K₈: Trace<int>, X₉: Trace<int> ::
//     !(K₈ == counter(0, 1, n₆)
//         && x₁₁ == current(X₉)
//         && X₉
//           == trace(0, for ⌊K₈⌋
//                       do x₄, k₇ ::
//                         case x₄ < 750000 => x₄ + 1 case 750000 <= x₄ => x₄ + 2)
//         && invs(for ⌊K₈⌋, ⌊X₉⌋ check k₇, x₄ :: x₄ < 1000000)
//         && 0 <= n₆
//         && 1000000 < x₁₁)
