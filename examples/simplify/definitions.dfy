// ./Cuvee.sh -simplify examples/simplify/definitions.dfy
// function definitions with :rw whose body is a match on a parameter give one rule per case,
// with disjoint patterns here, since overlapping ones are not treated specially; the lemmas vanish
datatype List<a> = Nil | Cons(head: a, tail: List<a>)
function {:rw} length<a>(xs: List<a>): int { match xs case Nil => 0 case Cons(_, ys) => 1 + length(ys) }
lemma length(Cons(1, Cons(2, Nil))) == 2
lemma forall x: int, xs: List<int> :: length(Cons(x, xs)) == length(xs) + 1
