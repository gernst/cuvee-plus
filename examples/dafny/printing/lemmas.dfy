// ./Cuvee.sh examples/dafny/printing/lemmas.dfy
// lemmas are printed as written, the conjunctions of the requires and ensures split into clauses,
// free lemmas without a body
function f(x: int): int

lemma {:rw} f_id(x: int)
  requires 0 <= x && x < 10
  ensures f(x) == x

lemma f_between<a>(x: int, y: a) returns (z: int)
  ensures f(x) <= z && z <= f(x) + 1
{}

lemma f_zero()
  ensures f(0) == 0
{}
