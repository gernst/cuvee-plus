// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/indp3.dfy
// SV-COMP array-fpi/indp3.yml (expected: safe), translated from the C program by hand: a[i] = (i
// - 1) * (i - 1), plus i twice, minus 1, which is checked to be i * i (indp4, indp5 are variants)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the arithmetic (i - 1) * (i - 1)
// + 2 i - 1 (indp4, indp5 are variants)

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  N := *;
  assume 0 < N;
  i := 0;
  while i < N {
    a := a[i := (i - 1) * (i - 1)];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] + i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] + i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] - 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == i * i;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
