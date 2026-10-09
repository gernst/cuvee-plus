// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_reverse_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_reverse_ground.yml (expected: safe), translated from the C
// program by hand: a is filled with arbitrary values, b is its reverse, which is checked element by element
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the reads of the copy at 100000
// - x - 1 are resolved by the stores at the counter positions

method main() {
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var x: int;
  var tmp: int;
  i := 0;
  while i < 100000 {
    havoc tmp;
    a := a[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    b := b[i := a[100000 - i - 1]];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert a[x] == b[100000 - x - 1];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
