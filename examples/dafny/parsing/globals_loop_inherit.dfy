// ./Cuvee.sh -quiet examples/dafny/parsing/globals_loop_inherit.dfy
// a loop without modifies clause may modify what its method may, by assignments and calls
var g: int; method p() modifies g { } method m() modifies g { while true { g := 1; p(); } }
