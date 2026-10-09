// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/brs1.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/brs1.yml (expected: safe), translated from the C program by hand: a is set
// to 1 where i % 1 == 0, i.e., everywhere, and sum adds the elements except the first, which is at most N; sum[0]
// of the one-element array as a scalar
//
// findings: the counter i has the cases 1 and i + 1 for i == 0 and otherwise, which agree, as in copysome1-1, and a
// lemma joins them; the sum is set in the first iteration and adds G(i) in the others, which a lemma states as c
// plus the sum of G(k + 1) over 0, ..., n - 2, shifted since the context of a map knows the range of its first
// dependency for counter(0, 1, n) only, where the guard of the elements, 0 < i < N, is decided; teq.dfy sums the
// constants; closed (no output)
// note: 2 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var sum: int;
  N := *;
  assume 0 < N <= 536870911;
  i := 0;
  while i < N {
    if i % 1 == 0 {
      a := a[i := 1];
    } else {
      a := a[i := 0];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i == 0 {
      sum := 0;
    } else {
      sum := sum + a[i];
    }
    i := i + 1;
  }
  assert sum <= N;
}

// remaining goals of -teq -simplify:
// none
