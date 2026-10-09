// ./Cuvee.sh examples/dafny/language/match_tuple.dfy
// a match on several values, match k, xs, is a match on their tuple, whose patterns are tuples of patterns, written
// without parentheses, which apply in order
datatype Nat = zero | succ(pred: Nat)
datatype List<a> = nil | cons(head: a, tail: List<a>)

function nth<a>(k: Nat, xs: List<a>, d: a): a
{
  match k, xs
  case _, nil => d
  case zero, cons(x, _) => x
  case succ(m), cons(_, ys) => nth(m, ys, d)
}
