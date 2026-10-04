// expected: invalid
// break leaves the loop before i == n

method early(n: int) returns (i: int)
  requires 0 <= n
  ensures i == n
{
  i := 0;
  while i < n
    invariant 0 <= i && i <= n
  {
    if i == 3 {
      break;
    }
    i := i + 1;
  }
}
