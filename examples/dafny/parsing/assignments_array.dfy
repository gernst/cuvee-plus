// ./Cuvee.sh examples/dafny/parsing/assignments_array.dfy
// assignments to elements are updates of arrays
method m(a: array<int, int>) returns (b: array<int, int>) { b := a; b[0] := 1; }
