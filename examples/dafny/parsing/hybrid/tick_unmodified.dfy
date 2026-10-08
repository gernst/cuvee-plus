// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid/tick_unmodified.dfy
var history: history<int>
method m(g: real) returns (x: real) { ode t :: x' == g; }
