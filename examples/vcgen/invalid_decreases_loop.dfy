// expected: invalid
// the measure of the loop does not decrease

method count(n: int) returns (k: int)
  requires 0 <= n
  ensures k == n
{
  k := 0;
  while k < n
    invariant k <= n
    decreases k
  {
    k := k + 1;
  }
}
