// ./Cuvee.sh examples/dafny/parsing/assignments/nested.dfy
method m(a: array<int, array<int, int>>) returns (b: array<int, array<int, int>>) { b := a; b[0][1] := 2; }
