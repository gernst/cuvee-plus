// ./Cuvee.sh -verify -z3 examples/dafny/vcgen/invalid_exit.dfy
// expected: invalid
// the invariant is too weak to establish i == n after the loop

method count(n: int) returns (i: int)
  requires 0 <= n
  ensures i == n
{
  i := 0;
  while i < n
    invariant 0 <= i
  {
    i := i + 1;
  }
}
