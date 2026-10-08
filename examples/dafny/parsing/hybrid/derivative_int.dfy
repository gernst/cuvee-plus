// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid/derivative_int.dfy
method m(n: int) returns (k: int) { k := (n :: n * n)'; }
