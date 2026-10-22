// ./Cuvee.sh -quiet examples/dafny/parsing/globals_call.dfy
var g: int; method m() modifies g { } method n() { m(); }
