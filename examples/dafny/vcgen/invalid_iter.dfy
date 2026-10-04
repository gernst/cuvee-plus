// expected: invalid
// nondeterministic iterations may stop before the loop has reached its goal

method count(n: int) returns (k: int)
  requires 0 <= n
  ensures k == n
{
  k := 0;
  while *
    invariant k <= n
  {
    if k < n {
      k := k + 1;
    }
  }
}
