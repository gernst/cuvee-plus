// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/invert_string-1.dfy
// SV-COMP ReachSafety-Loops/loops/invert_string-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of invert_string-3 with other constants or assertions; checks str1[i] == str2[j]

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  {
    var MAX: int;
    var str1: array<int, int>;
    var str2: array<int, int>;
    var cont: int;
    var i: int;
    var j: int;
    tmp₁ := *;
    assume 0 <= tmp₁;
    MAX := tmp₁;
    if !(MAX > 0) {
      assume false;
    }
    cont := 0;
    i := 0;
    while i < MAX {
      tmp₂ := *;
      str1 := str1[i := tmp₂];
      i := i + 1;
    }
    str1 := str1[MAX - 1 := 0];
    j := 0;
    i := MAX - 1;
    while i >= 0 {
      str2 := str2[j := str1[0]];
      j := j + 1;
      i := i - 1;
    }
    j := MAX - 1;
    i := 0;
    while i < MAX {
      assert str1[i] == str2[j];
      j := j - 1;
      i := i + 1;
    }
  }
}
