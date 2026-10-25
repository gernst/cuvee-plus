// ./Cuvee.sh -quiet examples/dafny/parsing/globals_loop_call.dfy
var g: int; var h: int; method p() modifies g { } method m() modifies g, h { while true modifies h { p(); } }
