// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/nla-digbench/ps6-ll.dfy
// SV-COMP nla-digbench/ps6-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of ps2-ll with other constants or assertions; checks -2*y*y*y*y*y*y - 6 * y*y*y*y*y - 5 *
// y*y*y*y + y*y + 12*x == 0; -2*y*y*y*y*y*y - 6 * y*y*y*y*y - 5 * y*y*y*y + y*y + 12*x == 0; k*y == y*y

method main() returns (result: int) {
  var k: int;
  var y: int;
  var x: int;
  var c: int;
  k := *;
  y := 0;
  x := 0;
  c := 0;
  while (1 != 0) {
    assert
      -2 * y * y * y * y * y * y - 6 * y * y * y * y * y - 5 * y * y * y * y
        + y * y
        + 12 * x
        == 0;
    if !(c < k) {
      break;
    }
    c := c + 1;
    y := y + 1;
    x := y * y * y * y * y + x;
  }
  assert
    -2 * y * y * y * y * y * y - 6 * y * y * y * y * y - 5 * y * y * y * y
      + y * y
      + 12 * x
      == 0;
  assert k * y == y * y;
  result := 0;
  return;
}
