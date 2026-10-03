// type inference for polymorphic functions such as == and array access

method id<a>(x: a) returns (y: a)
  ensures y == x
{
  y := x;
  assert y == x;
  assert x == y && y == y;
}

method lookup<a>(m: array<int,a>, i: int) returns (v: a)
  ensures v == m[i]
{
  v := m[i];
  assert v == m[i];
}
