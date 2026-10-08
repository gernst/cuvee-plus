// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid_derivative.dfy
// derivatives are with respect to variables on real
method m(x: real) returns (y: real) { y := (x :: x * x)'; }
