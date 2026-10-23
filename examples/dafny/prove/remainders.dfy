// ./Cuvee.sh -prove examples/dafny/prove/remainders.dfy
// remainders by a literal: their range 0 <= e % k < k decides comparisons, remainders modulo multiples of k are taken
// apart, e.g. of the overflow of unsigned integers of C, and a remainder whose argument is known to be in the range is
// the argument itself, also as the representative with the centered coefficients, e.g. x - 1 for x + 4294967295
lemma range(x: int)
  ensures 0 <= x % 4294967296 && x % 4294967296 < 4294967296

lemma nested(x: int, y: int)
  ensures (x % 4294967296 + y) % 4294967296 == (x + y) % 4294967296

lemma parity(x: int)
  ensures (2 * x % 4294967296) % 2 == 0

lemma inside(x: int)
  requires 0 <= x && x < 100
  ensures (x + 1) % 4294967296 == x + 1

lemma down(x: int)
  requires 0 < x && x < 100
  ensures (x + 4294967295) % 4294967296 == x - 1

lemma outside(x: int)
  requires 0 <= x
  ensures (x + 1) % 4294967296 == x + 1
