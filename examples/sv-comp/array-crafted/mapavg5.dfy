// ./Cuvee.sh -teq -simplify examples/sv-comp/array-crafted/mapavg5.dfy
// SV-COMP array-crafted/mapavg5.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of mapavg1 with other constants or assertions

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

var N: int;

method mapavg(x: array<int, int>) returns (result: int) {
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while i < N {
    ret := ret + i + x[i];
    i := i + 1;
  }
  result := (quotient(ret, N));
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
    ret := mapavg(x);
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    ret2 := mapavg(x);
    temp := x[0];
    i := 0;
    while i < N - 1 {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    ret5 := mapavg(x);
    if ret != ret2 || ret != ret5 {
      assert false;
    }
  }
  result := 1;
  return;
}
