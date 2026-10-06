// expected: valid
// the invariant of the loop is inferred

method main(n: int)
{
  var i: int;
  if 0 <= n {
    i := 0;
    while i < n
    {
      i := i + 1;
    }
    assert i == n;
  }
}
