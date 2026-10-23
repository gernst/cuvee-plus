// ./Cuvee.sh -prove examples/dafny/prove/rules_ground.dfy
// an equation of the context with a ground side is a rule without variables, in either direction
datatype box = box(v: int)
function f(x: int): int
function g(x: int): int
function h(b: box, c: box, x: int): bool { b.v == 0 && 1 == f(x) ==> g(b.v) == g(0) && g(f(x)) == g(1) && g(c.v) == g(0) }
