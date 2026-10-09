// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/Mono3_1.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/Mono3_1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks y!=0
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var x: int;
    var y: int;
    x := 0;
    y := 0;
    while x < N {
      if x < 500000 {
        y := y + 1;
      } else {
        y := y - 1;
      }
      x := x + 1;
    }
    assert y != 0;
  }
}
