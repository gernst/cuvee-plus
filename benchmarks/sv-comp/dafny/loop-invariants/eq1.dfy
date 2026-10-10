// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-invariants/eq1.dfy
// SV-COMP loop-invariants/eq1.yml (expected: safe), translated from the C program by hand: w and
// x, and y and z, start equal and are incremented or decremented together, which is checked; unsigned int is int,
// its wrap-around affects both alike
//
// findings: open: y and z are the current values of two traces with the same initial value and the same update,
// which differ only in the names of their bound variables, while expressions are compared literally, not modulo the
// names of bound variables (see TODO.md)

method main() {
  var w: int;
  var x: int;
  var y: int;
  var z: int;
  var b: int;
  var c: int;
  w := *;
  x := w;
  y := *;
  z := y;
  b := *;
  while b != 0 {
    c := *;
    if c != 0 {
      w := w + 1;
      x := x + 1;
    } else {
      y := y - 1;
      z := z - 1;
    }
    b := *;
  }
  assert w == x && y == z;
}

// remaining goals of -teq -simplify:
// goal
//   forall y₈: int, b₉: int, y₃₁: int, z₃₃: int, n₂₂: int, K₂₄: Trace<int>,
//          Y₂₅: Trace<int>, Z₂₇: Trace<int>, B₂₈: Trace<int>, C?₁₉: seq<int>,
//          B?₂₀: seq<int>, B?₂₁: seq<int> ::
//     K₂₄ == counter(0, 1, n₂₂)
//       && y₃₁ == current(Y₂₅)
//       && z₃₃ == current(Z₂₇)
//       && 0 == current(B₂₈)
//       && Y₂₅
//         == trace(y₈, for ⌊K₂₄⌋, C?₁₉
//                      do y₁₀, k₂₃, c₁₆ ::
//                        case c₁₆ != 0 => y₁₀ case c₁₆ == 0 => y₁₀ + -1)
//       && Z₂₇
//         == trace(y₈, for ⌊K₂₄⌋, C?₁₉
//                      do z₁₂, k₂₃, c₁₆ ::
//                        case c₁₆ != 0 => z₁₂ case c₁₆ == 0 => z₁₂ + -1)
//       && B₂₈
//         == trace(b₉, for ⌊K₂₄⌋, C?₁₉, B?₂₀, B?₂₁
//                      do b₁₃, k₂₃, c₁₆, b₁₇, b₁₈ ::
//                        case c₁₆ != 0 => b₁₇ case c₁₆ == 0 => b₁₈)
//       && invs(for ⌊K₂₄⌋, ⌊B₂₈⌋ check k₂₃, b₁₃ :: b₁₃ != 0)
//       && 0 <= n₂₂
//       ==> y₃₁ == z₃₃
