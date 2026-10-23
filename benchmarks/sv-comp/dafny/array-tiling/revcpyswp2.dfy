// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-tiling/revcpyswp2.dfy
// SV-COMP array-tiling/revcpyswp2.yml (expected: safe), translated from the C program by hand:
// a and b are reverse copies of arbitrary arrays, swapped twice element by element, and a is checked to be the
// reverse copy
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): reverse copies and two swaps

method main() {
  var S: int;
  var i: int;
  var tmp: int;
  var v: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var ac: array<int, int>;
  var bc: array<int, int>;
  S := *;
  if S > 1 {
    i := 0;
    while i < S {
      v := *;
      ac := ac[i := v];
      v := *;
      bc := bc[i := v];
      i := i + 1;
    }
    i := 0;
    while i < S {
      a := a[i := ac[S - i - 1]];
      b := b[i := bc[S - i - 1]];
      i := i + 1;
    }
    i := 0;
    while i < S {
      tmp := a[i];
      a := a[i := b[i]];
      b := b[i := tmp];
      i := i + 1;
    }
    i := 0;
    while i < S {
      tmp := a[i];
      a := a[i := b[i]];
      b := b[i := tmp];
      i := i + 1;
    }
    i := 0;
    while i < S {
      assert a[i] == ac[S - i - 1];
      i := i + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// none
