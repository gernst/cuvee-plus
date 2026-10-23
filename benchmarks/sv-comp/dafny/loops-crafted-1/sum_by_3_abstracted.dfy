// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops-crafted-1/sum_by_3_abstracted.dfy
// SV-COMP loops-crafted-1/sum_by_3_abstracted.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a program of the folder; checks (i+j+k)/3 <= SIZE

method main() returns (result: int)
{
  var n: int;
  var i: int;
  var k: int;
  var j: int;
  n := *;
  assume 0 <= n;
  i := 0;
  if i < n {
    i := *;
  assume 0 <= i;
    if !(i < n) {
      assume false;
    }
    if i < n {
      i := i + 1;
    }
    if i < n {
      assume false;
    }
  }
  j := i;
  while j < n {
    j := j + 1;
  }
  k := j;
  while k < n {
    k := k + 1;
  }
  assert (quot(i + j + k, 3)) <= n;
  result := 0;
  return;
}
