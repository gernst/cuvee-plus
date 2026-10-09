// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loop-acceleration/diamond_1-2.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/diamond_1-2.yml (expected: unsafe), translated from the C program by
// hand: the unsafe variant of diamond_1-1, which counts by 1 if y is even and by 2 otherwise
//
// findings: unsafe, not closed with the lemmas of diamond_1-1, as expected: the cases remain where the parity of x
// differs from that of y

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
  var x: int;
  var y: int;
  x := 0;
  havoc y;
  assume 0 <= y;
  while x < 99 {
    if y % 2 == 0 {
      x := x + 1;
    } else {
      x := x + 2;
    }
  }
  assert x % 2 == y % 2;
}

// remaining goals of -teq -simplify -split -simplify:
// goal forall y₃: int :: !(0 <= y₃ && y₃ % 2 == 0)
// goal forall y₃: int :: !(0 <= y₃ && y₃ % 2 == 1)
