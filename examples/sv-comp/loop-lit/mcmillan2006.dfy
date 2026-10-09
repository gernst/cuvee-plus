// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-lit/mcmillan2006.dfy
// SV-COMP loop-lit/mcmillan2006.yml (expected: safe), translated from the C program by hand: an
// array of arbitrary size n, at most 1000, is initialized to 0 and checked
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the initialization of an array
// of arbitrary size n is stores of a constant

method main() {
  var n: int;
  var x: array<int, int>;
  var i: int;
  n := *;
  assume 0 <= n <= 1000;
  i := 0;
  while i < n {
    x := x[i := 0];
    i := i + 1;
  }
  i := 0;
  while i < n {
    assert x[i] == 0;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
