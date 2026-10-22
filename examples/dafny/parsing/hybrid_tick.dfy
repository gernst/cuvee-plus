// ./Cuvee.sh -hybrid -quiet examples/dafny/parsing/hybrid_tick.dfy
// the history ticks after a differential equation
var history: history<int>
method m(g: real) returns (x: real) modifies history { ode t :: x' == g; }
