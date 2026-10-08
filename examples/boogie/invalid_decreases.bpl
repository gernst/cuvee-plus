// ./Cuvee.sh -verify -monomorph -z3 examples/boogie/invalid_decreases.bpl
// expected: invalid
// the measure of the loop does not decrease

procedure down(n: int) returns (r: int)
  requires 0 <= n;
  decreases n;
{
  var i: int;
  i := n;
  while (0 < i)
    invariant 0 <= i;
    decreases i + 1, 1;
  {
    i := i + 0;
  }
  if (0 < n) {
    call r := down(n - 1);
  }
}
