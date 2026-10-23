// ./Cuvee.sh -hybrid examples/dafny/parsing/hybrid.dfy
// derivatives with respect to variables on real, differential equations over the time t, after which the history
// ticks, and parallel composition of calls that do not share modified variables other than the history; that of other
// statements is parsed, but not verified
var history: history<int>
method derivative(x: real) returns (y: real) { y := (x :: x * x)'; }
method tick(g: real) returns (x: real) modifies history { ode t :: x' == g + t; }
method p(n: int) returns (x: int) modifies history assumes true commits true { x := n; }
method parallel_calls() returns (x: int, y: int) modifies history { parallel { x := p(1); y := p(2); } }
method parallel_other() returns (x: int, y: int) { parallel { x := 1; y := 2; } }
