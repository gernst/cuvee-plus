// ./Cuvee.sh -chc -entry main examples/dafny/parsing/horn_polymorphic.dfy
// the predicates of a polymorphic procedure with a body, also those of its program points, and its clauses are
// polymorphic in its type parameters, which Horn solvers do not support, hence the output is not passed to one
method id<a>(x: a) returns (y: a) { y := x; }
method main() { var z: int; z := id(1); assert z == 1; }
