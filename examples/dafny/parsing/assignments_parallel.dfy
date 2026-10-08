// ./Cuvee.sh examples/dafny/parsing/assignments_parallel.dfy
method m(a: array<int, int>) returns (b: array<int, int>, c: int) { b := a; b[0], c := 1, 2; }
