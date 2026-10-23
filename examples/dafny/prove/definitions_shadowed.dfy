// ./Cuvee.sh -prove examples/dafny/prove/definitions_shadowed.dfy
// the pattern variable ys shadows the parameter ys, the second argument is not the tail
datatype List<a> = Nil | Cons(head: a, tail: List<a>)
function {:rw} sum(xs: List<int>, ys: List<int>): int { match xs case Nil => 0 case Cons(y, ys) => y + sum(ys, ys) }
lemma sum_1()
  ensures sum(Cons(1, Cons(2, Nil)), Nil) == 3
{}
