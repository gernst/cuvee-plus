// ./Cuvee.sh -print null examples/dafny/parsing/invalid_arbitrary_element.dfy
// arbitrary values of elements of arrays and sequences are not supported
method m(a: array<int, int>) returns (b: array<int, int>) {
  b := a;
  b[0] := *;
}
