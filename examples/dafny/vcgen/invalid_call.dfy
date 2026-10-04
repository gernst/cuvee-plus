// expected: invalid
// the precondition of the callee is violated, the callee itself is correct

type checked {
  method pos(x: int) returns (y: int)
    requires 0 < x
    ensures y == x
  {
    y := x;
  }
}

method caller(c: checked) returns (z: int)
{
  z := c.pos(0);
}
