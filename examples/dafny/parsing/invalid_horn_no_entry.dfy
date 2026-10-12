// ./Cuvee.sh -chc examples/dafny/parsing/invalid_horn_no_entry.dfy
// Horn clauses need an entry point, which Dafny does not have without -entry
method f(x: int) returns (y: int) { y := x; }
