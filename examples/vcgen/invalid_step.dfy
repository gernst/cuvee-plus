// expected: invalid
// the invariant is not preserved

method down(n: int) returns (i: int)
  ensures i <= 0
{
  i := n;
  while 0 < i
    invariant i <= n
  {
    i := i + 1;
  }
}
