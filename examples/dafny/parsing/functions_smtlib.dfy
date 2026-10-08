// ./Cuvee.sh -print smt2 examples/dafny/parsing/functions_smtlib.dfy
// applications and lambdas are printed as in higher-order SMT-LIB, the declarations of the function types
// and of the application functions are not printed
function f(g: (int, int) -> int): int { g(1, 2) } function h(): (int, int) -> int { (x: int, y: int) => x }
