// ./Cuvee.sh -teq -simplify examples/sv-comp/array-crafted/bAnd3.dfy
// SV-COMP ReachSafety-Arrays/array-crafted/bAnd3.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of bAnd1 with other constants or assertions
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 10000

// the bit operations of C on integers, declared only
function bitand(a: int, b: int): int

method bAnd(x: array<int, int>) returns (result: int) {
  {
    var i: int;
    var res: int;
    res := x[0];
    i := 1;
    while i < 10000 {
      res := bitand(res, x[i]);
      i := i + 1;
    }
    result := res;
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
    ret := bAnd(x);
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    ret2 := bAnd(x);
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
    ret5 := bAnd(x);
    if ret != ret2 || ret != ret5 {
      assert false;
    }
    result := 1;
    return;
  }
}
