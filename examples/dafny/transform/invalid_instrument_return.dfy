// ./Cuvee.sh -instrument examples/dafny/transform/invalid_instrument_return.dfy
// return in an inlined implementation would leave the caller
function f(x: int): int

method {:implement f(x)} g(x: int) returns (y: int)
{
  y := x;
  return;
}

method m(x: int) returns (y: int)
{
  y := f(x);
}
