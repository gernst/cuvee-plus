// ./Cuvee.sh -verify -z3 examples/dafny/vcgen/invalid_decreases_call.dfy
// expected: invalid
// the measure of the recursive call is not bounded from below

method down(n: int) returns (k: int)
  ensures k == 0
  decreases n
{
  if n == 0 {
    k := 0;
  } else {
    k := down(n - 1);
  }
}
