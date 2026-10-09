// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/geo2-ll.dfy
// SV-COMP ReachSafety-Loops/nla-digbench/geo2-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of geo1-ll with other constants or assertions; checks 1 + x*z - x - z*y == 0; 1 + x*z - x -
// z*y == 0

method main() returns (result: int) {
  {
    var z: int;
    var k: int;
    var x: int;
    var y: int;
    var c: int;
    z := *;
    k := *;
    x := 1;
    y := 1;
    c := 1;
    while (1 != 0) {
      assert 1 + x * z - x - z * y == 0;
      if !(c < k) {
        break;
      }
      c := c + 1;
      x := x * z + 1;
      y := y * z;
    }
    assert 1 + x * z - x - z * y == 0;
    result := 0;
    return;
  }
}
