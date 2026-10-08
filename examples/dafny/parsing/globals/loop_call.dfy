// ./Cuvee.sh -print null examples/dafny/parsing/globals/loop_call.dfy
var g: int; method p() modifies g { } method m() modifies g { while true { p(); } }
