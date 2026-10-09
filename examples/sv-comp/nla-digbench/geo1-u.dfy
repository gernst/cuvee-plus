// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/geo1-u.dfy
// SV-COMP nla-digbench/geo1-u.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks x*z - x - y + 1 == 0; 1 + x - y == 0

method main() returns (result: int) {
  var z: int;
  var k: int;
  var x: int;
  var y: int;
  var c: int;
  z := *;
  assume 0 <= z;
  k := *;
  assume 0 <= k;
  x := 1;
  y := z;
  c := 1;
  while (1 != 0) {
    assert x * z - x - y + 1 == 0;
    if !(c < k) {
      break;
    }
    c := c + 1;
    x := x * z + 1;
    y := y * z;
  }
  x := x * (z - 1);
  assert 1 + x - y == 0;
  result := 0;
  return;
}
