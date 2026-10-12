// ./Cuvee.sh -chc -entry g examples/dafny/parsing/horn_entry.dfy
// the entry point g, where executions start (-entry), the precondition of f is inferred from its call in g
method f(x: int) returns (y: int) { y := x; }
method g(x: int) returns (y: int) { y := f(x); }
