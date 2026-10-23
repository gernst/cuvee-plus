// ./Cuvee.sh -prove examples/dafny/simplify/rules_equations.dfy
// a variable of the expression is matched like the right-hand side of its equation in the context
function f(x: int): int
function g(x: int): int
axiom {:rw} forall x: int :: f(g(x)) == x
function h(y: int, z: int): bool { y == g(z) ==> f(y) == z }
