// ./Cuvee.sh -teq -simplify examples/sv-comp/array-crafted/mapavg3.dfy
// SV-COMP ReachSafety-Arrays/array-crafted/mapavg3.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mapavg1 with other constants or assertions
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 10000

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

method mapavg(x: array<int, int>) returns (result: int) {
  {
    var i: int;
    var ret: int;
    ret := 0;
    i := 0;
    while i < 10000 {
      ret := ret + i + x[i];
      i := i + 1;
    }
    result := (quotient(ret, 10000));
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
    ret := mapavg(x);
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    ret2 := mapavg(x);
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
    ret5 := mapavg(x);
    if ret != ret2 || ret != ret5 {
      assert false;
    }
    result := 1;
    return;
  }
}
