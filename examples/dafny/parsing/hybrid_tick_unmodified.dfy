// ./Cuvee.sh -hybrid -quiet examples/dafny/parsing/hybrid_tick_unmodified.dfy
var history: history<int>
method m(g: real) returns (x: real) { ode t :: x' == g; }
