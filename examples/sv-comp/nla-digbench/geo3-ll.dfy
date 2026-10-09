// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/geo3-ll.dfy
// SV-COMP ReachSafety-Loops/nla-digbench/geo3-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of geo1-ll with other constants or assertions; checks z*x - x + a - az*y == 0; z*x - x + a
// - az*y == 0

method main() returns (result: int) {
  {
    var z: int;
    var a: int;
    var k: int;
    var x: int;
    var y: int;
    var c: int;
    var az: int;
    z := *;
    a := *;
    k := *;
    x := a;
    y := 1;
    c := 1;
    az := a * z;
    while (1 != 0) {
      assert z * x - x + a - az * y == 0;
      if !(c < k) {
        break;
      }
      c := c + 1;
      x := x * z + a;
      y := y * z;
    }
    assert z * x - x + a - az * y == 0;
    result := x;
    return;
  }
}
