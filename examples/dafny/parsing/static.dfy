// ./Cuvee.sh examples/dafny/parsing/static.dfy
// static members of a datatype have no `this` and only the type parameters that their signature mentions (b of
// pair<a, b> for second and valid); they are called without `this` inside the type and qualified by the type outside
datatype pair<a, b> = pair(fst: a, snd: b)
{
  static function second(x: b, y: b): b { y }

  static predicate valid(y: b)

  static method make(x: a, y: b) returns (p: pair<a, b>)
  {
    p := pair(x, y);
  }

  function swapped(): pair<b, a> { pair(snd, fst) }

  method copy() returns (p: pair<a, b>)
    requires valid(snd)
  {
    p := make(fst, second(snd, snd));
  }
}

method m(x: int, y: bool) returns (p: pair<int, bool>)
  requires pair.valid(y)
{
  p := pair.make(x, pair.second(y, y));
}
