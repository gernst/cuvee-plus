// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid/tick.dfy
// the history ticks after a differential equation
var history: history<int>
method m(g: real) returns (x: real) modifies history { ode t :: x' == g; }
