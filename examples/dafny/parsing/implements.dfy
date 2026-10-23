// ./Cuvee.sh examples/dafny/parsing/implements.dfy
// implementations name the function that they implement by a pattern, resolved in the scope of their inputs, this
// included, the members of a datatype that defines a sort of the prelude and top-level functions
datatype {:implements} set<a> = Nil | Cons(head: a, tail: set<a>)
{
  function {:implements x in this} member(x: a): bool
  function {:implements |this|} card(): int
  function {:implements this + t} union(t: set<a>): set<a>
}

function {:implements {x}} singleton<a>(x: a): set<a> { Cons(x, Nil) }
