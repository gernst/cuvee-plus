// ./Cuvee.sh -teq -simplify examples/sv-comp/array-crafted/mapsum2.dfy
// SV-COMP ReachSafety-Arrays/array-crafted/mapsum2.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mapsum1 with other constants or assertions
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000

method mapsum(x: array<int, int>) returns (result: int) {
  {
    var i: int;
    var ret: int;
    ret := 0;
    i := 0;
    while i < 1000 {
      ret := ret + i + x[i];
      i := i + 1;
    }
    result := ret;
    return;
  }
}

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  assume 0 < N;
  {
    var x: array<int, int>;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    {
      var i: int;
      i := 0;
      while i < N {
        tmp₁ := *;
        x := x[i := tmp₁];
        i := i + 1;
      }
    }
    ret := mapsum(x);
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    ret2 := mapsum(x);
    temp := x[0];
    {
      var i: int;
      i := 0;
      while i < N - 1 {
        x := x[i := x[i + 1]];
        i := i + 1;
      }
    }
    x := x[N - 1 := temp];
    ret5 := mapsum(x);
    if ret != ret2 || ret != ret5 {
      assert false;
    }
    result := 1;
    return;
  }
}
