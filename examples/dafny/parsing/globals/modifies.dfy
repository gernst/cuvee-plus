// ./Cuvee.sh -print null examples/dafny/parsing/globals/modifies.dfy
var g: int; method m() modifies g ensures g == old(g) + 1 { g := g + 1; }
