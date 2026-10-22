// ./Cuvee.sh -quiet examples/dafny/parsing/assignments_call.dfy
method p() returns (x: int) method m(a: array<int, int>) returns (b: array<int, int>) { b := a; b[0] := p(); }
