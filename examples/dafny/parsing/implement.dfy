// ./Cuvee.sh examples/dafny/parsing/implement.dfy
// implementations name the function that they implement by a pattern, resolved in the scope of their inputs, this
// included, the members of a datatype that defines a sort of the prelude and top-level functions
datatype {:implement} set<a> = Nil | Cons(head: a, tail: set<a>)
{
  function {:implement x in this} member(x: a): bool
  function {:implement |this|} card(): int
  function {:implement this + t} union(t: set<a>): set<a>
}

function {:implement {x}} singleton<a>(x: a): set<a> { Cons(x, Nil) }
