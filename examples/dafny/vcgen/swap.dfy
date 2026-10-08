// ./Cuvee.sh -verify -z3 examples/dafny/vcgen/swap.dfy
// expected: valid
// simultaneous assignment

method swap(x: int, y: int) returns (a: int, b: int)
  ensures a == y && b == x
{
  a, b := x, y;
  a, b := b, a;
  assert a == y;
}
