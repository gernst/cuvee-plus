// expected: valid
// arithmetic and comparison are overloaded for int and real

procedure diff(a: real, b: real) returns (c: real)
  requires a < b;
  ensures a < a + c && a - c < b - c;
{
  c := b - a;
}
