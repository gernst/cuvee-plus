// expected: valid
// continue (not Boogie) must re-establish the invariant

procedure odd(n: int) returns (c: int)
  requires 0 <= n;
  ensures c <= n;
{
  var i: int;
  i := 0;
  c := 0;
  while (i < n)
    invariant 0 <= i && i <= n && c <= i;
  {
    i := i + 1;
    if (i mod 2 == 0) {
      continue;
    }
    c := c + 1;
  }
}
