// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid/ode_int.dfy
method m(g: int) returns (x: int) { ode t :: x' == g; }
