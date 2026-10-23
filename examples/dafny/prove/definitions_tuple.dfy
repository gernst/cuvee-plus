// ./Cuvee.sh -prove examples/dafny/prove/definitions_tuple.dfy
// a definition by a match on a tuple of its parameters gives a rule per case, whose patterns replace the parameters
datatype Nat = zero | succ(pred: Nat)
datatype List<a> = nil | cons(head: a, tail: List<a>)

function {:rw} nth<a>(k: Nat, xs: List<a>, d: a): a
{
  match k, xs
  case _, nil => d
  case zero, cons(x, _) => x
  case succ(m), cons(_, ys) => nth(m, ys, d)
}

goal nth(succ(zero), cons(1, cons(2, nil)), 0) == 2

goal forall k: Nat, d: int :: nth(k, nil, d) == d

goal forall k: Nat, x: int, xs: List<int>, d: int :: nth(succ(k), cons(x, xs), d) == nth(k, xs, d)
