// ./Cuvee.sh -simplify examples/dafny/simplify/definitions_unfolded.dfy
// other definitions are unfolded
datatype List<a> = Nil | Cons(head: a, tail: List<a>)
function {:rw} f(xs: List<int>): int { 0 }
lemma f(Nil) == 0
