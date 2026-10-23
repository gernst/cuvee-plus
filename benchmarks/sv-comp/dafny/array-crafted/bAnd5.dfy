// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-crafted/bAnd5.dfy
// SV-COMP array-crafted/bAnd5.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of bAnd1 with other constants or assertions

// the bit operations of C on integers, declared only
function {:c} bitand(a: int, b: int): int

var N: int;

method bAnd(x: array<int, int>) returns (result: int) {
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while i < N {
    res := bitand(res, x[i]);
    i := i + 1;
  }
  result := res;
  return;
}

method main() returns (result: int)
  modifies N
  requires N == 0
{
  var tmp₁: int;
  var x: array<int, int>;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var i: int;
  N := *;
  if N > 1 {
    i := 0;
    while i < N {
      tmp₁ := *;
      x := x[i := tmp₁];
      i := i + 1;
    }
    ret := bAnd(x);
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    ret2 := bAnd(x);
    temp := x[0];
    i := 0;
    while i < N - 1 {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    ret5 := bAnd(x);
    if ret != ret2 || ret != ret5 {
      assert false;
    }
  }
  result := 1;
  return;
}
