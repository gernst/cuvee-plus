// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/string-2.dfy
// SV-COMP ReachSafety-Loops/loops/string-2.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of string-1 with other constants or assertions; checks found == 0 || found == 1

// the bit operations of C on integers, declared only
function shl(a: int, b: int): int

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  {
    var string_A: array<int, int>;
    var string_B: array<int, int>;
    var i: int;
    var j: int;
    var nc_A: int;
    var nc_B: int;
    var found: int;
    found := 0;
    i := 0;
    while i < 5 {
      tmp₁ := *;
      string_A := string_A[i := tmp₁];
      i := i + 1;
    }
    if string_A[5 - 1] != 0 {
      result := 0;
      return;
    }
    i := 0;
    while i < 5 {
      tmp₂ := *;
      string_B := string_B[i := tmp₂];
      i := i + 1;
    }
    if string_B[5 - 1] != 0 {
      result := 0;
      return;
    }
    nc_A := 0;
    while string_A[nc_A] != 0 {
      nc_A := nc_A + 1;
    }
    nc_B := 0;
    while string_B[nc_B] != 0 {
      nc_B := nc_B + 1;
    }
    if !(nc_B >= nc_A) {
      result := 0;
      return;
    }
    j := 0;
    i := j;
    while i < nc_A && j < nc_B {
      if string_A[i] == string_B[j] {
        i := i + 1;
        j := j + 1;
      } else {
        i := i - j + 1;
        j := 0;
      }
    }
    found := shl((if j > nc_B - 1 then 1 else 0), i);
    assert found == 0 || found == 1;
    result := 0;
    return;
  }
}
