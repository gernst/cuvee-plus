// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/overflow_1-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/overflow_1-1.yml (expected: safe), translated from the C program by
// hand: x starts at 10 and is increased by 2 until it wraps around below 10, which keeps it even; the wrap-around
// of unsigned int is modeled by % 2^32
//
// findings: the wrap-around is modeled by % 2^32, and a lemma states that an update by (x + c) % m keeps the
// remainder modulo every d that divides c and m; closed (no output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// an update by x + c modulo m keeps the remainder of x modulo every d that divides c and m, e.g. the parity of a value
// that is increased by an even step and wraps around at 2^32; the side conditions are closed once c, m, d are known
lemma {:rw} {:free} {:teq} forall x0: int, n: int, c: int, m: int, d: int ::
  if 0 < d && 0 < m && c % d == 0 && m % d == 0
  then current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: (x + c) % m)) % d == x0 % d

method main() {
  var x: int;
  x := 10;
  while x >= 10 {
    x := (x + 2) % 4294967296;
  }
  assert x % 2 == 0;
}

// remaining goals of -teq -simplify:
// none
