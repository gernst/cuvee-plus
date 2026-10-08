// ./Cuvee.sh examples/dafny/language/match.dfy
// match expressions, with constructor patterns, nested ones, variables, and wildcards,
// with and without braces around the cases
datatype List<a> = Nil | Cons(head: a, tail: List<a>)

function length<a>(xs: List<a>): int
{
  match xs
  case Nil => 0
  case Cons(_, ys) => 1 + length(ys)
}

function firsts(xs: List<int>): int
{
  match xs {
    case Cons(x, Cons(y, _)) => x + y
    case other => 0
  }
}
