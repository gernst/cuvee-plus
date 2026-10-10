// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/nec40.dfy
// SV-COMP loops/nec40.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: a variant of nec11 with other constants or assertions; checks 0
// note: the global variables of the C program, zero there, are local; of the array x, only x[0] == 0 is kept,
// since the loop copies x up to its first zero, which is x[0]

method main() returns (result: int) {
  var x: array<int, int>;
  var y: array<int, int>;
  var i: int;
  var j: int;
  var k: int;
  x := x[0 := 0];
  k := *;
  i := 0;
  while x[i] != 0 {
    y := y[i := x[i]];
    i := i + 1;
  }
  y := y[i := 0];
  if k >= 0 && k < i {
    if y[k] != 0 {
      assert (0 != 0);
    }
  }
  result := 0;
  return;
}
