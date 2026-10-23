// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-tiling/pnr5.dfy
// SV-COMP array-tiling/pnr5.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of pnr2 with other constants or assertions; checks a[i]!=DEFAULTVAL

method ReadFromPort() returns (result: int) {
  var tmp₁: int;
  var x: int;
  tmp₁ := *;
  x := tmp₁;
  result := x;
  return;
}

var SIZE: int;


method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0 
{
  var i: int;
  var value: int;
  var a: array<int, int>;
  var DEFAULTVAL: int;
  var FIXEDVAL: int;
  SIZE := *;
  if SIZE > 1 {
    DEFAULTVAL := 0;
    FIXEDVAL := 10;
    if (rem(SIZE, 5)) != 0 {
      result := 1;
      return;
    }
    assume (rem(SIZE, 5)) == 0;
    i := 1;
    while i <= (quot(SIZE, 5)) {
      value := ReadFromPort();
      if value != DEFAULTVAL {
        a := a[i * 5 - 5 := value];
      } else {
        a := a[i * 5 - 5 := FIXEDVAL];
      }
      value := ReadFromPort();
      if value != DEFAULTVAL {
        a := a[i * 5 - 4 := value];
      } else {
        a := a[i * 5 - 4 := FIXEDVAL];
      }
      value := ReadFromPort();
      if value != DEFAULTVAL {
        a := a[i * 5 - 3 := value];
      } else {
        a := a[i * 5 - 3 := FIXEDVAL];
      }
      value := ReadFromPort();
      if value != DEFAULTVAL {
        a := a[i * 5 - 2 := value];
      } else {
        a := a[i * 5 - 2 := FIXEDVAL];
      }
      value := ReadFromPort();
      if value != DEFAULTVAL {
        a := a[i * 5 - 1 := value];
      } else {
        a := a[i * 5 - 1 := FIXEDVAL];
      }
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      assert a[i] != DEFAULTVAL;
      i := i + 1;
    }
  }
  result := 1;
  return;
}
