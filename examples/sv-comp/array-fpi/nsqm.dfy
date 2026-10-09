// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-fpi/nsqm.dfy
// SV-COMP array-fpi/nsqm.yml (expected: safe), translated from the C program by hand: b holds
// the odd numbers by a recurrence, and a the squares plus N, from N + 1 and the partial sums of b plus 2, as sqm
//
// findings: the recurrences of sqm with the first element N + 1, with the same lemmas; closed (no output)
// note: 3 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  N := *;
  assume 0 < N <= 536870911;
  b := b[0 := 1];
  a := a[0 := N + 1];
  i := 1;
  while i < N {
    b := b[i := b[i - 1] + 2];
    i := i + 1;
  }
  i := 1;
  while i < N {
    a := a[i := a[i - 1] + b[i - 1] + 2];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == N + (i + 1) * (i + 1);
    i := i + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
