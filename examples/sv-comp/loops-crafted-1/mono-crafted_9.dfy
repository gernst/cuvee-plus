// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_9.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/mono-crafted_9.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mono-crafted_1 with other constants or assertions; checks y==x
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var x: int;
    var y: int;
    x := 0;
    y := 500000;
    while x < N {
      if x < 500000 {
        x := x + 1;
      } else {
        x := x + 1;
        y := y + 1;
      }
    }
    assert y == x;
    result := 0;
    return;
  }
}
