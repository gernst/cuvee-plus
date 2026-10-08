// ./Cuvee.sh -hybrid -print null examples/dafny/parsing/hybrid/shared.dfy
var history: history<int>
method p(n: int) returns (x: int) modifies history assumes true commits true { x := n; }
method m() returns (x: int) modifies history { parallel { x := p(1); x := p(2); } }
