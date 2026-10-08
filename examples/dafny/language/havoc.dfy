// ./Cuvee.sh examples/dafny/language/havoc.dfy
// havoc gives variables arbitrary values, not Dafny, but printed for specifications without conditions
method m(n: int) returns (x: int, y: int) {
  x := n;
  havoc x, y;
  havoc y;
}
