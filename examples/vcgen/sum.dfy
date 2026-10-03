// expected: valid
// loop with invariants, local variable

method sum(n: int) returns (s: int)
  requires 0 <= n
  ensures 2 * s == n * (n + 1)
{
  var i: int;
  i := 0;
  s := 0;
  while i < n
    invariant 0 <= i && i <= n
    invariant 2 * s == i * (i + 1)
  {
    i := i + 1;
    s := s + i;
  }
}
