// ./Cuvee.sh -print lean examples/dafny/printing/lean.dfy
// the logic in Lean 4: datatypes with selectors axiomatized by their values on the constructors, declared and defined
// functions, axioms, free lemmas as axioms, the other lemmas as theorems, rewrite rules as simp lemmas, and goals as
// examples; booleans are propositions, sequences lists, arrays functions, and tuples products
datatype List<a> = Nil | Cons(head: a, tail: List<a>)

function length<a>(xs: List<a>): int {
  match xs
  case Nil => 0
  case Cons(_, ys) => 1 + length(ys)
}

function f(x: int): int

function g(s: seq<int>, a: array<int, int>, i: int): int {
  if i < |s| then s[i] + a[i] else a[i := 0][i]
}

axiom forall x: int :: f(x) >= 0

lemma {:rw} length_nil<a>()
  ensures length(Nil as List<a>) == 0

lemma f_pos(x: int)
  requires x > 0
  ensures exists y: int :: f(y) < x
{}

goal forall x: int, b: bool :: (b ==> f(x) >= 0) && (var p: (int, bool) := (x, b); p.1 == b) && 0 < 1
