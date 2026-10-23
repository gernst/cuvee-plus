// finite sets as lists without duplicates, the implementation of -include impl:listset (see ideas/implementations.md):
// the datatype defines the sort set of the prelude, its members implement the functions on sets with a receiver,
// the top-level functions those without one
datatype {:impl} {:implements} set<a> = Nil | Cons(head: a, tail: set<a>)
{
  function {:impl} {:implements x in this} member(x: a): bool
  {
    match this
    case Nil => false
    case Cons(y, r) => y == x || r.member(x)
  }

  function {:impl} {:implements |this|} card(): int
  {
    match this
    case Nil => 0
    case Cons(_, r) => 1 + r.card()
  }

  // the head is not in the rest, hence it is in the union of the rest and t if and only if it is in t
  function {:impl} {:implements this + t} union(t: set<a>): set<a>
  {
    match this
    case Nil => t
    case Cons(y, r) => if t.member(y) then r.union(t) else Cons(y, r.union(t))
  }
}

function {:impl} {:implements {}} empty<a>(): set<a> { Nil }

function {:impl} {:implements {x}} singleton<a>(x: a): set<a> { Cons(x, Nil) }
