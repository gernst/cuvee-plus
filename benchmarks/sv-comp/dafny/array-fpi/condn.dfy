// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/dafny/array-fpi/condn.dfy
// SV-COMP array-fpi/condn.yml (expected: safe), translated from the C program by hand: a is
// filled with arbitrary values, which are capped at N, and are at most N then
//
// findings: a clamp of each element to N, a store guarded by a comparison of the element at the position of the
// iteration, which is still the initial element; the lemma reads it as N where the initial element is at least N; a
// generic guard C(a[k], k) is no pattern, since a[k] is a term over bound variables, and C(a, k) would be unsound;
// -split splits the conditional; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var tmp: int;
  N := *;
  assume 0 < N;
  i := 0;
  while i < N {
    tmp := *;
    a := a[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] < N {
      a := a[i := a[i]];
    } else {
      a := a[i := N];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] <= N;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
