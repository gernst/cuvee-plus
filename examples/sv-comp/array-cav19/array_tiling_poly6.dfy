// ./Cuvee.sh -teq -simplify examples/sv-comp/array-cav19/array_tiling_poly6.dfy
// SV-COMP array-cav19/array_tiling_poly6.yml (expected: safe), translated from the C program by hand:
// a[i] = (i - 1) * (i + 1), then a[i] - i * i, which is checked to be -1 (long long is int)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): (k - 1) * (k + 1) - k * k is -1

method main() {
  var S: int;
  var i: int;
  var a: array<int, int>;
  S := *;
  assume S > 1;
  i := 0;
  while i < S {
    a := a[i := (i - 1) * (i + 1)];
    i := i + 1;
  }
  i := 0;
  while i < S {
    a := a[i := a[i] - i * i];
    i := i + 1;
  }
  i := 0;
  while i < S {
    assert a[i] == -1;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
