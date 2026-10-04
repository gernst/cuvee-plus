// expected: valid
// conditionals, assertion with equality

procedure max(x: int, y: int) returns (m: int)
  ensures x <= m && y <= m;
  ensures m == x || m == y;
{
  if (x < y) {
    m := y;
  } else {
    m := x;
  }
  assert m == x || m == y;
}
