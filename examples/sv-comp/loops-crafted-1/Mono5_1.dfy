// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/Mono5_1.dfy
// SV-COMP loops-crafted-1/Mono5_1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of Mono3_1 with other constants or assertions; checks z!=0
// note: the concrete loop bounds are symbolic, arbitrary positive values: y for 10000000

method main() returns (result: int) {
  {
    var x: int;
    var y: int;
    var z: int;
    x := 0;
    y := *;
    assume 0 < y;
    z := 5000000;
    while x < y {
      if x >= 5000000 {
        z := z - 1;
      }
      x := x + 1;
    }
    assert z != 0;
  }
}
