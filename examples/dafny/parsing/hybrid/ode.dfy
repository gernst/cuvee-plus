// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid/ode.dfy
method m(g: real) returns (x: real) { ode t :: x' == g + t; }
