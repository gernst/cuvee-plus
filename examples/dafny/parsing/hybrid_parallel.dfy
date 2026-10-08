// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid_parallel.dfy
// parallel composition of calls that do not share modified variables other than the history
var history: history<int>
method p(n: int) returns (x: int) modifies history assumes true commits true { x := n; }
method m() returns (x: int, y: int) modifies history { parallel { x := p(1); y := p(2); } }
