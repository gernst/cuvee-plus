// expected: invalid
// the precondition of a method without body is a goal at the call

method dec(x: int) returns (y: int)
  requires 0 < x
  ensures y == x - 1

method main(x: int)
{
  var y: int;
  y := dec(x);
}
