// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops-crafted-1/sumt7.dfy
// SV-COMP loops-crafted-1/sumt7.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of sumt2 with other constants or assertions; checks (i+j+k+v1+v2+v3+v4) == l


method main() returns (result: int)
{
  var n: int;
  var i: int;
  var k: int;
  var j: int;
  var l: int;
  var v1: int;
  var v2: int;
  var v3: int;
  var v4: int;
  n := 0;
  i := 0;
  k := 0;
  j := 0;
  l := 0;
  v1 := 0;
  v2 := 0;
  v3 := 0;
  v4 := 0;
  n := *;
  while l < n {
    if !(((rem(l, 7))) != 0) {
      v1 := v1 + 1;
    } else if !(((rem(l, 6))) != 0) {
      v2 := v2 + 1;
    } else if !(((rem(l, 5))) != 0) {
      v3 := v3 + 1;
    } else if !(((rem(l, 4))) != 0) {
      v4 := v4 + 1;
    } else if !(((rem(l, 3))) != 0) {
      i := i + 1;
    } else if !(((rem(l, 2))) != 0) {
      j := j + 1;
    } else {
      k := k + 1;
    }
    l := l + 1;
    assert i + j + k + v1 + v2 + v3 + v4 == l;
  }
  result := 0;
  return;
}
