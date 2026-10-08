// ./Cuvee.sh -fuse examples/dafny/simplify/fuse.dfy
// fixpoint fusion of two defined functions, whose definitions match on a list, into a single recursive function,
// printed as a function whose cases match all arguments, which constructs no intermediate list: the doubled list
// is summed, and taken up to k, whose test stays in the fused function; id produces no constructor, such that sum
// is applied to its result as a function value
datatype List = Nil | Cons(head: int, tail: List)

function dbl(xs: List): List {
  match xs
  case Nil => Nil
  case Cons(y, ys) => Cons(y + y, dbl(ys))
}

function sum(xs: List): int {
  match xs
  case Nil => 0
  case Cons(y, ys) => y + sum(ys)
}

function take(xs: List, k: int): int {
  match xs
  case Nil => 0
  case Cons(y, ys) => if 0 < k then y + take(ys, k - 1) else 0
}

function id(xs: List): List {
  match xs
  case Nil => Nil
  case Cons(y, ys) => Cons(y, id(ys))
}

fuse sum(dbl(xs)) = ???
fuse take(dbl(xs), k) = ???
fuse sum(id(xs)) = ???
