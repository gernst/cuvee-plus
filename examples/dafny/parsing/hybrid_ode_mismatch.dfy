// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid_ode_mismatch.dfy
method m(g: int) returns (x: real) { ode t :: x' == t + g; }
