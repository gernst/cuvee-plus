// ./Cuvee.sh -teq -simplify examples/sv-comp/array-crafted/xor1.dfy
// SV-COMP array-crafted/xor1.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder
// note: merges xor2, xor3 and xor4, which differ only in the bound (1000, 10000, 100000)
// note: the concrete loop bounds are symbolic: N for 100, which is passed to xor, and at least 2, since x[0] and
// x[1] are swapped

// the bit operations of C on integers, declared only
function bitxor(a: int, b: int): int

method xor(x: array<int, int>, N: int) returns (result: int) {
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while i < N {
    res := bitxor(res, x[i]);
    i := i + 1;
  }
  result := res;
  return;
}

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var x: array<int, int>;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var i: int;
  assume 1 < N;
  i := 0;
  while i < N {
    tmp₁ := *;
    x := x[i := tmp₁];
    i := i + 1;
  }
  ret := xor(x, N);
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  ret2 := xor(x, N);
  temp := x[0];
  i := 0;
  while i < N - 1 {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[N - 1 := temp];
  ret5 := xor(x, N);
  if ret != ret2 || ret != ret5 {
    assert false;
  }
  result := 1;
  return;
}
