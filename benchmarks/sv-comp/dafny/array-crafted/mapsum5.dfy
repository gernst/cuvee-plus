// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-crafted/mapsum5.dfy
// SV-COMP array-crafted/mapsum5.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mapsum1 with other constants or assertions

var N: int;

method mapsum(x: array<int, int>) returns (result: int) {
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while i < N {
    ret := ret + i + x[i];
    i := i + 1;
  }
  result := ret;
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
    ret := mapsum(x);
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    ret2 := mapsum(x);
    temp := x[0];
    i := 0;
    while i < N - 1 {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    ret5 := mapsum(x);
    if ret != ret2 || ret != ret5 {
      assert false;
    }
  }
  result := 1;
  return;
}
