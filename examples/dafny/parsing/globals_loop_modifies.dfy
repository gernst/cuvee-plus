// ./Cuvee.sh -quiet examples/dafny/parsing/globals_loop_modifies.dfy
var g: int; method p() modifies g { } method m() { while true modifies g { } }
