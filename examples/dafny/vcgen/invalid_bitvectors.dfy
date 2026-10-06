// expected: invalid
// the increment of a bitvector wraps around

method incr(x: bv8) returns (y: bv8)
  ensures y > x
{
  y := x + 1;
}
