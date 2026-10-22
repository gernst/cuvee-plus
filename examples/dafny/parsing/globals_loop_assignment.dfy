// ./Cuvee.sh -quiet examples/dafny/parsing/globals_loop_assignment.dfy
var g: int; method p() modifies g { } method m() modifies g { while true { g := 1; } }
