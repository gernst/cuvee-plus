// ./Cuvee.sh examples/dafny/language/arbitrary.dfy
// the right-hand side * gives variables arbitrary values, also in initializers of locals; an assignment with stars is
// the parallel assignment of the other right-hand sides, which read the values before it, followed by a havoc of the
// variables assigned *, which is printed as := * again
method m(n: int) returns (x: int, y: int) {
  var z: int := *;
  x := n;
  x, y := *, x;
  y := *;
}
