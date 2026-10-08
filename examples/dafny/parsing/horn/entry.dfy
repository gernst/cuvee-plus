// ./Cuvee.sh -chc examples/dafny/parsing/horn/entry.dfy
// the entry points are the procedures that are not called, here g
method f(x: int) returns (y: int) { y := x; }
method g(x: int) returns (y: int) { y := f(x); }
