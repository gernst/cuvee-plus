// ./Cuvee.sh -hybrid -quiet examples/dafny/parsing/hybrid_ode.dfy
method m(g: real) returns (x: real) { ode t :: x' == g + t; }
