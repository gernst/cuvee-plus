// ./Cuvee.sh -print null examples/dafny/parsing/globals_loop.dfy
// loops modify the global variables in their modifies clause only, which must be modifiable by the method
var g: int; method p() modifies g { } method m() modifies g { while true modifies g { g := 1; p(); } }
