// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_copy1_ground-1.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_copy1_ground-1.yml (expected: safe), translated from the C
// program by hand: a1 is filled with arbitrary values and copied into a2, which then equals a1
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the copy is stores at the
// counter positions

method main() {
  var a1: array<int, int>;
  var a2: array<int, int>;
  var a: int;
  var i: int;
  var x: int;
  var tmp: int;
  a := 0;
  while a < 100000 {
    havoc tmp;
    a1 := a1[a := tmp];
    a := a + 1;
  }
  i := 0;
  while i < 100000 {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a1[x] == a2[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
