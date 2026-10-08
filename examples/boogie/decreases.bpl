// ./Cuvee.sh -verify -monomorph -z3 examples/boogie/decreases.bpl
// expected: valid
// termination measures of procedures and loops, which are not Boogie

procedure down(n: int) returns (r: int)
  requires 0 <= n;
  decreases n;
{
  var i: int;
  i := n;
  while (0 < i)
    invariant 0 <= i;
    decreases i, 1;
  {
    i := i - 1;
  }
  if (0 < n) {
    call r := down(n - 1);
  }
}
