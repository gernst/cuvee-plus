// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/underapprox_1-2.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/underapprox_1-2.yml (expected: safe), translated from the C program
// by hand: y is doubled 6 times, starting from 1, and a power of 2 is not divisible by 3
//
// findings: y is doubled in each iteration, a geometric sequence, which the lemma accelerates to x0 * pow(c, n)
// with the auxiliary function pow, which is not unfolded, such that the iterations are not unrolled, and a lemma
// from number theory states that powers of 2 are not divisible by 3; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// powers, an auxiliary function, which is not unfolded
function pow(c: int, n: int): int

// a power of 2 is not divisible by 3, since 3 is a prime other than 2 (number theory, not about traces)
lemma {:rw} {:free} {:teq} forall n: int ::
  (pow(2, n) % 3 == 0) <==> false

method main() {
  var x: int;
  var y: int;
  x := 0;
  y := 1;
  while x < 6 {
    x := x + 1;
    y := y * 2;
  }
  assert y % 3 != 0;
}

// remaining goals of -teq -simplify:
// none
