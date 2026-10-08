// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid/read.dfy
var history: history<int>
method p(n: int) returns (x: int) modifies history assumes true commits true { x := n; }
method m() returns (x: int, y: int) modifies history { parallel { x := p(1); y := p(x); } }
