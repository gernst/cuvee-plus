// ./Cuvee.sh -verify -z3 examples/dafny/vcgen/locals.dfy
// expected: valid
// initialized locals, by expressions and by a method call
datatype d = d(f: int) { method get() returns (r: int) ensures r == 7 }

method m(x: int, s: d) returns (y: int)
  ensures y == x + 3 + 7
{
  var a: int := x + 1;
  var b: int, c: bool := a + 1, true;
  var r: int := s.get();
  var u: int;
  y := b + 1 + r;
  { var v: int := 5; u := v; }
}
