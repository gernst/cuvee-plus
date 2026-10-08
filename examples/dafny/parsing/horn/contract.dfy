// ./Cuvee.sh -chc -print null examples/dafny/parsing/horn/contract.dfy
// the predicates of procedures with a body replace their contracts
method f(x: int) returns (y: int) ensures y == x { y := x; }
