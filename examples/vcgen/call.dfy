// expected: valid
// method calls are replaced by the callee's contract

type util {
  method inc(x: int) returns (y: int)
    ensures y == x + 1
  {
    y := x + 1;
  }
}

method add2(u: util, x: int) returns (z: int)
  ensures z == x + 2
{
  var y: int;
  y := u.inc(x);
  z := u.inc(y);
}

method again(u: util, x: int) returns (x_: int)
  ensures x_ == x + 1
{
  x_ := x;
  x_ := u.inc(x_);
}
