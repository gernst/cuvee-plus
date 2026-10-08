// ./Cuvee.sh -simplify examples/simplify/rules_dafny.dfy
// rewrite rules are assertions and lemmas with the attribute :rw
function f(x: int): int
function g(x: int): int
predicate p(x: int)
axiom {:rw} forall x: int :: f(g(x)) == x
lemma {:rw} forall x: int :: 0 <= x ==> p(x)
function h(a: int): bool { f(g(a)) == a && p(1) }
