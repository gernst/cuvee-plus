// ./Cuvee.sh examples/dafny/parsing/globals.dfy
// methods modify the global variables in their modifies clause, old(e) refers to their values at the entry; loops
// modify those in their modifies clause only, which must be modifiable by the method
var g: int
method inc() modifies g ensures g == old(g) + 1 { g := g + 1; }
method p() modifies g { }
method loop() modifies g { while true modifies g { g := 1; p(); } }
