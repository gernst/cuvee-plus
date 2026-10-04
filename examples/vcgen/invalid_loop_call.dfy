// expected: invalid
// calls in a loop modify the global variables that the callee modifies

var g: int;

method inc()
  modifies g
{
  g := g + 1;
}

method m(n: int)
  modifies g
  requires 0 < n
{
  var i: int;
  g := 0;
  i := 0;
  while i < n
    invariant i <= n
  {
    inc();
    i := i + 1;
  }
  assert g == 0;
}
