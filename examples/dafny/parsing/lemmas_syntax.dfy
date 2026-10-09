// ./Cuvee.sh -print smt2 examples/dafny/parsing/lemmas_syntax.dfy
// lemmas are written as in Dafny and are the formula forall xs :: requires ==> exists ys :: ensures, the conjunctions
// of the clauses, without quantifiers if there are no variables and without the implication if there are no requires,
// named by :named; a lemma without a body is free, one with the empty body is to be proved
function f(x: int): int

lemma {:rw} f_id(x: int)
  requires 0 <= x
  requires x < 10
  ensures f(x) == x

lemma f_between<a>(x: int, y: a) returns (z: int)
  ensures f(x) <= z
  ensures z <= f(x) + 1
{}

lemma f_zero()
  ensures f(0) == 0
{}
