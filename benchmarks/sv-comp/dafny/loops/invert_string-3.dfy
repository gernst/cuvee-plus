// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/invert_string-3.dfy
// SV-COMP loops/invert_string-3.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of invert_string-1 with other constants or assertions; checks str1[i] == str2[j]

method main() returns (result: int) {
  var tmp₁: int;
  var max: int;
  var str1: array<int, int>;
  var str2: array<int, int>;
  var i: int;
  var j: int;
  max := 5;
  i := 0;
  while i < max {
    tmp₁ := *;
    str1 := str1[i := tmp₁];
    i := i + 1;
  }
  str1 := str1[max - 1 := 0];
  j := 0;
  i := max - 1;
  while i >= 0 {
    str2 := str2[j := str1[i]];
    j := j + 1;
    i := i - 1;
  }
  j := max - 1;
  i := 0;
  while i < max {
    assert str1[i] == str2[j];
    j := j - 1;
    i := i + 1;
  }
}
