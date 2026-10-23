// finite sets as lists without duplicates, the implementation of -include implement:listset
// (see ideas/implementations.md): the datatype defines the sort set of the prelude, its members implement the
// functions on sets with a receiver, the top-level functions those without one
datatype {:implement} set<a> = Nil | Cons(head: a, tail: set<a>)
{
  function {:implement x in this} member(x: a): bool
  {
    match this
    case Nil => false
    case Cons(y, r) => y == x || r.member(x)
  }

  function {:implement |this|} card(): int
  {
    match this
    case Nil => 0
    case Cons(_, r) => 1 + r.card()
  }

  // the head is not in the rest, hence it is in the union of the rest and t if and only if it is in t
  function {:implement this + t} union(t: set<a>): set<a>
  {
    match this
    case Nil => t
    case Cons(y, r) => if t.member(y) then r.union(t) else Cons(y, r.union(t))
  }
}

function {:implement {}} empty<a>(): set<a> { Nil }

function {:implement {x}} singleton<a>(x: a): set<a> { Cons(x, Nil) }
