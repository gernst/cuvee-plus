// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_init3_ground-2.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_init3_ground-2.yml (expected: safe), translated from the C
// program by hand: a is initialized three times, to 42, 43, and 44, and is 44 then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the last of the three
// initializations overwrites all positions

method main() {
  var a: array<int, int>;
  var i: int;
  var x: int;
  i := 0;
  while i < 100000 {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    a := a[i := 43];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    a := a[i := 44];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a[x] == 44;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
