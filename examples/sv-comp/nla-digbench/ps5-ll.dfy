// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/ps5-ll.dfy
// SV-COMP nla-digbench/ps5-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of ps2-ll with other constants or assertions; checks 6*y*y*y*y*y + 15*y*y*y*y + 10*y*y*y -
// 30*x - y == 0; 6*y*y*y*y*y + 15*y*y*y*y + 10*y*y*y - 30*x - y == 0; k*y == y*y

method main() returns (result: int) {
  var k: int;
  var y: int;
  var x: int;
  var c: int;
  k := *;
  assume k <= 256;
  y := 0;
  x := 0;
  c := 0;
  while (1 != 0) {
    assert
      6 * y * y * y * y * y + 15 * y * y * y * y + 10 * y * y * y - 30 * x - y
        == 0;
    if !(c < k) {
      break;
    }
    c := c + 1;
    y := y + 1;
    x := y * y * y * y + x;
  }
  assert
    6 * y * y * y * y * y + 15 * y * y * y * y + 10 * y * y * y - 30 * x - y
      == 0;
  assert k * y == y * y;
  result := 0;
  return;
}
