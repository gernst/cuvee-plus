// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_vector_difference_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_vector_difference_ground.yml (expected: safe), translated from
// the C program by hand: a and b are filled with arbitrary values and c is their difference element by element
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  var i: int;
  var x: int;
  var tmp: int;
  i := 0;
  while i < 100000 {
    havoc tmp;
    a := a[i := tmp];
    havoc tmp;
    b := b[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    c := c[i := a[i] - b[i]];
    i := i + 1;
  }
  x := 0;
  while x < 100000 {
    assert c[x] == a[x] - b[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
