// expected: valid
// leaving a loop with break, the loop condition is not known afterwards

method find(n: int, k: int) returns (i: int)
  requires 0 <= k && k < n
  ensures i == k
{
  i := 0;
  while i < n
    invariant 0 <= i && i <= k
  {
    if i == k {
      break;
    }
    i := i + 1;
  }
}
