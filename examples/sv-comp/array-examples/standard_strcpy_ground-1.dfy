// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_strcpy_ground-1.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_strcpy_ground-1.yml (expected: safe), translated from the C program by hand:
// src is copied into dst up to the first 0, and the copied prefix is checked to agree
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the loop test reads the source,
// which -teq records in the iteration constraints

method main() {
  var i: int;
  var j: int;
  var x: int;
  var v: int;
  var src: array<int, int>;
  var dst: array<int, int>;
  i := 0;
  j := 0;
  while j < 100000 {
    havoc v;
    src := src[j := v];
    j := j + 1;
  }
  while i < 100000 && src[i] != 0 {
    dst := dst[i := src[i]];
    i := i + 1;
  }
  x := 0;
  while x < i {
    assert dst[x] == src[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
