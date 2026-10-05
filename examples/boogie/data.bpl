// expected: valid
// datatypes as in Dafny with the keyword data, which is not Boogie,
// whose constructors and selectors are functions
data Stack<a> = empty | push(top: a, pop: Stack<a>);

data Pair = pair(fst: int, snd: bool);

procedure peek(x: int, s: Stack<int>) returns (y: int)
  ensures y == x;
{
  y := top(push(x, s));
}

procedure first(p: Pair) returns (x: int)
  ensures x == fst(p);
{
  x := fst(pair(fst(p), snd(p)));
}
