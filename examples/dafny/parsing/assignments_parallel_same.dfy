// ./Cuvee.sh -quiet examples/dafny/parsing/assignments_parallel_same.dfy
// elements of the same variable cannot be assigned at once, since the variable would be assigned twice
method m(a: array<int, int>) returns (b: array<int, int>) { b := a; b[0], b[1] := b[1], b[0]; }
