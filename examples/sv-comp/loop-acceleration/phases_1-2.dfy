// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loop-acceleration/phases_1-2.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/phases_1-2.yml (expected: unsafe), translated from the C program by
// hand: the unsafe variant of phases_1-1, whose first phase ends at 65521 (0xfff1), which is odd, such that x stays
// odd
//
// findings: unsafe, not closed with the lemmas of phases_1-1, as expected: the second phase starts at the odd 65521
// note: 1 of its lemmas are part of teq.dfy now and are removed here

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// a counter in two phases: by 1 up to the bound b, from an initial value up to b, then by c
lemma {:rw} {:free} {:teq} forall x0: int, n: int, b: int, c: int ::
  if x0 <= b
  then current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x < b => x + 1 case b <= x => x + c))
         == if n <= b - x0 then x0 + n else b + (n - (b - x0)) * c

method main() {
  var x: int;
  x := 0;
  while x < 268435455 {
    if x < 65521 {
      x := x + 1;
    } else {
      x := x + 2;
    }
  }
  assert x % 2 == 0;
}

// remaining goals of -teq -simplify -split -simplify:
// goal
//   forall n₃: int, K₅: Trace<int>, X₆: Trace<int> ::
//     !(K₅ == counter(0, 1, n₃)
//         && X₆
//           == trace(0, for ⌊K₅⌋
//                       do x₂, k₄ ::
//                         case x₂ < 65521 => x₂ + 1 case 65521 <= x₂ => x₂ + 2)
//         && invs(for ⌊K₅⌋, ⌊X₆⌋ check k₄, x₂ :: x₂ < 268435455)
//         && 134250488 <= n₃)
