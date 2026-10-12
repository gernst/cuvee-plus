// ./Cuvee.sh -vcgen -monomorph -z3 examples/boogie/vcgen/data.bpl
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

// mutually recursive datatypes are declared together, joined by and
data Tree<a> = node(value: a, children: Forest<a>)
and Forest<a> = leaf | grow(first: Tree<a>, rest: Forest<a>);

procedure root(t: Tree<int>) returns (x: int)
  ensures x == value(t);
{
  x := value(node(value(t), children(t)));
}
