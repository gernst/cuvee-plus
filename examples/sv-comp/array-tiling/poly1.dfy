// ./Cuvee.sh -teq -simplify examples/sv-comp/array-tiling/poly1.dfy
// SV-COMP ReachSafety-Arrays/array-tiling/poly1.yml (expected: safe), translated from the C program by hand:
// a[i] = i * i, which is checked (long long is int)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var S: int;
  var i: int;
  var a: array<int, int>;
  havoc S;
  if S > 1 && S < 100000 {
    i := 0;
    while i < S {
      a := a[i := i * i];
      i := i + 1;
    }
    i := 0;
    while i < S {
      assert a[i] == i * i;
      i := i + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// none
