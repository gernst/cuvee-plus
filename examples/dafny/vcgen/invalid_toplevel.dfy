// expected: invalid
// the precondition of a call statement does not hold
datatype counter = counter(n: int)
{
  method tick() requires this.n >= 0
}

method inc(x: int) returns (y: int)
  ensures y == x + 1

method validate(x: int)
  requires x > 0

method m(x: int, c: counter) returns (z: int)
  requires x > 0 && c.n >= 0
  ensures z == x + 2
{
  var y: int := inc(x);
  validate(x - 1);
  c.tick();
  z := inc(y);
}
