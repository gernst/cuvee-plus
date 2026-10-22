// ./Cuvee.sh -hybrid -quiet examples/dafny/parsing/hybrid_derivative_int.dfy
method m(n: int) returns (k: int) { k := (n :: n * n)'; }
