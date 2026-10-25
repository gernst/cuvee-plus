// ./Cuvee.sh -vcgen -z3 examples/dafny/vcgen/loop_call_global.dfy
// expected: invalid
// a loop without modifies clause that calls a method modifies the global variables of the method's modifies clause,
// which the call carries (see Call): g is havocked at the head of the loop, h is not, hence keeps(n) holds, and
// changes(n) does not (its loop has an invariant, such that its refutation is a counterexample)

var g: int
var h: int

method inc()
  modifies g
  ensures g == old(g) + 1

method keeps(n: int)
  modifies g, h
{
  var i: int;
  i := 0;
  h := 0;
  while i < n
  {
    inc();
    i := i + 1;
  }
  assert h == 0;
}

method changes(n: int)
  modifies g, h
{
  var i: int;
  i := 0;
  g := 0;
  while i < n
    invariant 0 <= g
  {
    inc();
    i := i + 1;
  }
  assert g == 0;
}
