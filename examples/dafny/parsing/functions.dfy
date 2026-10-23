// ./Cuvee.sh examples/dafny/parsing/functions.dfy
// function values: applications of parameters, of constants, and of variables of function type, which come before
// functions of the same name, lambdas, curried ones, and function types of ten arguments
function c(): int -> int
function apply_constant(): int { c(1) }
function apply(g: (int, bool) -> int): int { g(1, true) }
function g(x: int): bool
function apply_variable(g: int -> int): int { g(1) }
function lambda(): (int, bool) -> int { (x: int, b: bool) => if b then x else 0 }
function curried(): int -> bool -> int { (x: int) => (b: bool) => x }
function ten(g: (int, int, int, int, int, int, int, int, int, int) -> int): bool { true }
