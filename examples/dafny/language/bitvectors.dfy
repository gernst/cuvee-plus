// ./Cuvee.sh examples/dafny/language/bitvectors.dfy
// expected: valid
// bitvectors, whose arithmetic wraps around, and whose division and comparisons are unsigned;
// numeric literals are bitvectors where the context requires it, and integers otherwise

method wrap(x: bv8) returns (y: bv8)
  requires x == 255
  ensures y == 0 && y as int == 0 && y < x
{
  y := x + 1;
}

method ops(x: bv8, y: bv8) returns (z: bv8)
  ensures z == x & y ^ (x & y)
  ensures !(!z) == z && -(-z) == z
  ensures z <= 255 && z / 1 == z && z % 1 == 0
{
  z := 0;
}

// conversions from and to integers, and between widths, which truncate or extend by zeros
method conv(n: int) returns (b: bv16)
  requires 0 <= n < 256
  ensures b as int == n && (b as bv8) as int == n && (b as bv8) as bv16 == b
{
  b := n as bv16;
}
