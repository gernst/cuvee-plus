// ./Cuvee.sh -print null examples/dafny/parsing/globals/call.dfy
var g: int; method m() modifies g { } method n() { m(); }
