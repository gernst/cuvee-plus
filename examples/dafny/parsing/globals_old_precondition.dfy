// ./Cuvee.sh -verify -z3 examples/dafny/parsing/globals_old_precondition.dfy
// the precondition is evaluated at the entry, where old(e) is e
var g: int; method m() modifies g requires old(g) == 0 ensures g == 1 { g := g + 1; }
