// ./Cuvee.sh -verify -z3 examples/dafny/vcgen/return.dfy
// expected: valid
// return must establish the postcondition, also from within a loop

method sign(x: int) returns (s: int)
  ensures (x < 0 ==> s == -1) && (0 <= x ==> s == 1)
{
  s := -1;
  if x < 0 {
    return;
  }
  s := 1;
}

method first(n: int) returns (i: int)
  requires 0 < n
  ensures i == 0
{
  i := 0;
  while i < n
    invariant 0 <= i
  {
    return;
  }
  i := 0;
}
