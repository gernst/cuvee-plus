// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/underapprox_1-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/underapprox_1-1.yml (expected: unsafe), translated from the C program
// by hand: the unsafe variant of underapprox_1-2, which asserts that y, which is 64, is not 64
//
// findings: unsafe, not closed with the lemmas of underapprox_1-2, as expected: pow(2, 6) is 64, which the lemmas
// do not evaluate either
// note: 1 of its lemmas are part of teq.dfy now and are removed here

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// powers, an auxiliary function, which is not unfolded
function pow(c: int, n: int): int

// a power of 2 is not divisible by 3, since 3 is a prime other than 2 (number theory, not about traces)
lemma {:rw} {:teq} pow_1(n: int)
  ensures (pow(2, n) % 3 == 0) <==> false

method main() {
  var x: int;
  var y: int;
  x := 0;
  y := 1;
  while x < 6 {
    x := x + 1;
    y := y * 2;
  }
  assert y != 64;
}

// remaining goals of -teq -simplify:
// goal 64 != pow(2, 6)
