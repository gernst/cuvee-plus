// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/underapprox_2-1.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/underapprox_2-1.yml (expected: unsafe), translated from the C program
// by ./Cuvee.sh -print dfy: a variant of underapprox_1-1 with other constants or assertions; checks x != 6

method main() returns (result: int) {
  {
    var x: int;
    var y: int;
    x := 0;
    y := 1;
    while x < 6 {
      x := x + 1;
      y := y * 2;
    }
    assert x != 6;
  }
}
