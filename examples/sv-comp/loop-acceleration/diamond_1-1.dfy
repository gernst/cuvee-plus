// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loop-acceleration/diamond_1-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/diamond_1-1.yml (expected: safe), translated from the C program by
// hand: x counts by 2 if y is even, by 1 otherwise, up to 99, and has the parity of y then, unsigned in C
//
// findings: the guard of the update depends only on y, which the loop does not modify; the lemma splits such a
// trace into one of two traces, chosen by the guard, each of which teq.dfy accelerates to a counter; the hypothesis
// X == (if y % 2 == 0 then counter(0, 2, n) else counter(0, 1, n)) is split into cases by -split, and a second
// -simplify closes both, given that the remainder modulo 2 is 0 or 1 (without that lemma, 0 <= y && y % 2 != 0 ==>
// 1 == y % 2 remains); closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary values that keep the verdict: N for 99, which is odd

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>

// a trace whose cases are decided by a condition c that is the same in all iterations, i.e., c does not depend
// on the bound variables, which a variable of the lemma cannot capture, is one of two traces, chosen by c
lemma {:rw} {:free} {:teq} forall x0: int, i: int, d: int, n: int, c: bool, F: (int, int) -> int, G: (int, int) -> int ::
  trace(x0, for ⌊counter(i, d, n)⌋ do x, k :: case c => F(x, k) case !c => G(x, k))
    == if c then trace(x0, for ⌊counter(i, d, n)⌋ do x, k :: F(x, k))
       else trace(x0, for ⌊counter(i, d, n)⌋ do x, k :: G(x, k))

// the remainder modulo 2 is 0 or 1
lemma {:rw} {:free} {:teq} forall y: int ::
  !(y % 2 == 0) <==> y % 2 == 1

method main() {
  var N: int;
  var x: int;
  var y: int;
  assume 0 < N && N % 2 == 1;
  x := 0;
  y := *;
  assume 0 <= y;
  while x < N {
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + 1;
    }
  }
  assert x % 2 == y % 2;
}

// remaining goals of -teq -simplify -split -simplify:
// none
