// ./Cuvee.sh -chc -entry f examples/dafny/parsing/horn_contract.dfy
// the contract of a procedure with a body is checked: its precondition at the calls, here the entry, since it is
// not called, and its postcondition at the exit, as goals in the heads of clauses
method f(x: int) returns (y: int) ensures y == x { y := x; }
