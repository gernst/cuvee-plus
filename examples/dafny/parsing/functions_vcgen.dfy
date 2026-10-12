// ./Cuvee.sh -vcgen -z3 examples/dafny/parsing/functions_vcgen.dfy
// the declarations of the function types are not passed to solvers
var g: int; method m() modifies g ensures g == 1 { g := 1; }
