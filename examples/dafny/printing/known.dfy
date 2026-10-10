// ./Cuvee.sh -print c -known dfy,teq,rw examples/dafny/printing/known.dfy
// the C program alone: -known drops the prelude of Dafny (dfy), the lemmas over the types of teq.dfy, which it
// declares in the input (teq), and the functions marked rw, whose calls the C printer writes as division
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

lemma {:teq} length_reflexive(xs: List<int>)
  ensures length(xs) == length(xs)

method main() {
  var x: int;
  x := *;
  assume 0 <= x;
  assert quotient(x, 2) <= x;
}
