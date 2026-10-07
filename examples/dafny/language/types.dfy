// types with members, and datatypes with members, accessed on variables
type foo {
  function f(x: int): int
  method m(x: int) returns (y: int)
}

datatype color
  = red | green | blue

datatype baz<a>
  = good(that: a) | bad
{
  predicate isGood()
  {
    this != bad()
  }
}

method test(b: foo)
{
  var y: int;
  y := b.f(1);
  y := b.m(1);
}