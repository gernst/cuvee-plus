// ./Cuvee.sh -prove examples/dafny/prove/rewrite_polymorphic.dfy
// the type parameters of a rule are instantiated, here with int, and annotations e as T of the expression are skipped
datatype List<a> = nil | cons(head: a, tail: List<a>)
function length<a>(xs: List<a>): int
predicate p(n: int)
lemma {:rw} length_1<a>()
  ensures length(nil as List<a>) == 0
{}
lemma {:rw} length_2<a>(y: a, xs: List<a>)
  ensures length(cons(y, xs)) == length(xs) + 1
{}
axiom p(length(cons(1, cons(2, nil as List<int>))))
