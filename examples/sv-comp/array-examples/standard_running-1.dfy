// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_running-1.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_running-1.yml (expected: unsafe), translated from the C
// program by hand: the unsafe variant of standard_running-2, whose second test resets the flag for a negative
// element whose entry in b is 0, which it always is
//
// findings: unsafe, not closed with the lemma of standard_running-2, as expected: the goal states that the flag is
// reset, which it is

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>

// two cases that store at the same position are one store of a conditional value, which teq.dfy introduces as
// stores; the guard of the second case must follow from the negation of the first
lemma {:rw} {:free} {:teq} forall a0: array<int, int>, n: int, hs: seq<int>,
                           C: (int, int) -> bool, F: (int, int) -> int, G: (int, int) -> int ::
  trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: case C(k, h) => a[k := F(k, h)] case !C(k, h) => a[k := G(k, h)])
    == trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: a[k := if C(k, h) then F(k, h) else G(k, h)])

method main() {
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var f: int;
  var tmp: int;
  i := 0;
  while i < 100000 {
    havoc tmp;
    a := a[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    if a[i] >= 0 {
      b := b[i := 1];
    } else {
      b := b[i := 0];
    }
    i := i + 1;
  }
  f := 1;
  i := 0;
  while i < 100000 {
    if a[i] >= 0 && b[i] == 0 {
      f := 0;
    }
    if a[i] < 0 && b[i] == 0 {
      f := 0;
    }
    i := i + 1;
  }
  assert f != 0;
}

// remaining goals of -teq -simplify:
// goal
//   forall Tmp?₁₀: seq<int>, K₃₄: Trace<int>, F₃₅: Trace<int>, I₃₆: Trace<int> ::
//     !(K₃₄ == counter(0, 1, 100000)
//         && 0 == current(F₃₅)
//         && F₃₅
//           == trace(1, for ⌊K₃₄⌋, ⌊I₃₆⌋
//                       do f₃₀, k₃₃, i₃₁ ::
//                         case (if 0 <= earlier(k₃₃, Tmp?₁₀) then 1 else 0)
//                           == 0 => 0
//                         case 0 <= earlier(k₃₃, Tmp?₁₀) => f₃₀)
//         && I₃₆ == counter(0, 1, 100000))
