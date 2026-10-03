// expected: valid
// calls to top-level methods, with and without results, and member calls without results
datatype counter = counter(n: int)
{
  method tick() requires this.n >= 0
}

method inc(x: int) returns (y: int)
  ensures y == x + 1

method check(x: int)
  requires x > 0

method m(x: int, c: counter) returns (z: int)
  requires x > 0 && c.n >= 0
  ensures z == x + 2
{
  var y: int := inc(x);
  check(x);
  c.tick();
  z := inc(y);
}
