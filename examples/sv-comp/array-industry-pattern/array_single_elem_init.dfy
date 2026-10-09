// ./Cuvee.sh -teq -simplify examples/sv-comp/array-industry-pattern/array_single_elem_init.dfy
// SV-COMP ReachSafety-Arrays/array-industry-pattern/array_single_elem_init.yml (expected: unsafe), translated from the C program by hand:
// a[i] = 1 and b[i] = i % 2 if q == 0, else a[i] = 0, and c[i] is set from b[i] if a[i] != 0; then a[15000] =
// 1, and c[15000] == 0 is checked, which is arbitrary unless q was 0 at 15000
//
// findings: unsafe: c[15000] is arbitrary unless q was 0 there; open, as expected

method main() {
  var i: int;
  var q: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  i := 0;
  while i < 100000 {
    q := *;
    a := a[i := 0];
    if q == 0 {
      a := a[i := 1];
      b := b[i := i % 2];
    }
    if a[i] != 0 {
      if b[i] == 0 {
        c := c[i := 0];
      } else {
        c := c[i := 1];
      }
    }
    i := i + 1;
  }
  a := a[15000 := 1];
  i := 0;
  while i < 100000 {
    if i == 15000 {
      assert c[i] == 0;
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall c₅: array<int, int>, c₂₅: array<int, int>, K₁₅: Trace<int>,
//          I₁₆: Trace<int>, C₂₀: Trace<array<int, int>>, Q?₁₂: seq<int> ::
//     K₁₅ == counter(0, 1, 100000)
//       && c₂₅ == current(C₂₀)
//       && I₁₆ == counter(0, 1, 100000)
//       && C₂₀
//         == trace(c₅, for ⌊K₁₅⌋, ⌊I₁₆⌋, Q?₁₂
//                      do c₁₀, k₁₄, i₆, q₁₁ ::
//                        case q₁₁ == 0 && k₁₄ % 2 == 0 => c₁₀[k₁₄ := 0]
//                        case q₁₁ == 0 && k₁₄ % 2 != 0 => c₁₀[k₁₄ := 1]
//                        case q₁₁ != 0 => c₁₀)
//       ==> c₂₅[15000] == 0
