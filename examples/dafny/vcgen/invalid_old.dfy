// ./Cuvee.sh -verify -z3 examples/dafny/vcgen/invalid_old.dfy
// expected: invalid
// the value at the entry is not the current one

var count: int;

method inc(n: int)
  modifies count
  requires 0 < n
  ensures count == old(count)
{
  count := count + n;
}
