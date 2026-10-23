// ./Cuvee.sh -teq -entry main examples/dafny/teq/globals_calls.dfy
// symbolic execution of global variables, old, and calls: a call of a procedure without a contract is inlined (inc),
// one of a procedure with a contract is by the contract (dbl): its precondition is checked, its result and the
// modified global variable take fresh values, and its postcondition is assumed, where old(g) is the value at the call
var g: int

method inc(x: int) returns (y: int)
  modifies g
{
  y := x + 1;
  g := g + 1;
}

method dbl(x: int) returns (y: int)
  modifies g
  requires 0 <= x
  ensures y == 2 * x && g == old(g) + x

method main() returns (r: int)
  modifies g
  ensures r == 4 && g == old(g) + 3
{
  r := inc(1);
  r := dbl(r);
}
