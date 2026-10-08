// ./Cuvee.sh -print null examples/dafny/parsing/globals/loop_modifies.dfy
var g: int; method p() modifies g { } method m() { while true modifies g { } }
