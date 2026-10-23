// ./Cuvee.sh -prove examples/boogie/prove/rules_boogie.bpl
// rewrite rules are assertions and lemmas with the attribute :rw
function f(x: int): int;
function g(x: int): int;
axiom {:rw} (forall x: int :: f(g(x)) == x);
lemma {:rw} (forall x: int :: !(f(x) < 0));
function h(a: int): bool { f(g(a)) == a && !(f(a) < 0) }
