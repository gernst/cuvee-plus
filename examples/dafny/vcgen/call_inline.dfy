// ./Cuvee.sh -vcgen -z3 examples/dafny/vcgen/call_inline.dfy
// calls of procedures with a body and without a contract are inlined, the others are by their contract
method inc(x: int) returns (y: int) { y := x + 1; }

method dbl(x: int) returns (y: int) ensures y == 2 * x

method main() returns (r: int)
  ensures r == 4
{
  r := inc(1);
  r := dbl(r);
}
