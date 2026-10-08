// ./Cuvee.sh -print null examples/dafny/parsing/functions/apply.dfy
// variables of function type before functions of the same name, then constants of function type, then members
function f(g: (int, bool) -> int): int { g(1, true) }
