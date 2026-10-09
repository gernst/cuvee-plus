// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_partition_ground-1.dfy
// SV-COMP array-examples/standard_partition_ground-1.yml (expected: unsafe), translated from the
// C program by ./Cuvee.sh -print dfy: a variant of standard_partition_ground-2 with other constants or assertions;
// checks bb[ x ] >= 0; cc[ x ] < 0
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  assume 0 < N;
  {
    var aa: array<int, int>;
    var a: int;
    var b: int;
    var c: int;
    var bb: array<int, int>;
    var cc: array<int, int>;
    var x: int;
    a := 0;
    b := 0;
    c := 0;
    while a < N {
      tmp₁ := *;
      aa := aa[a := tmp₁];
      if aa[a] >= 0 {
        bb := bb[b := aa[a]];
        b := b + 1;
      }
      a := a + 1;
    }
    a := 0;
    while a < N {
      if aa[a] >= 0 {
        cc := cc[c := aa[a]];
        c := c + 1;
      }
      a := a + 1;
    }
    x := 0;
    while x < b {
      assert bb[x] >= 0;
      x := x + 1;
    }
    x := 0;
    while x < c {
      assert cc[x] < 0;
      x := x + 1;
    }
    result := 0;
    return;
  }
}
