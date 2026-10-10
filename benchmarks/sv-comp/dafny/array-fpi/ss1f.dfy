// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/ss1f.dfy
// SV-COMP array-fpi/ss1f.yml (expected: unsafe), translated from the C program by hand: the
// unsafe variant of ss1, whose elements are 2 initially
//
// findings: unsafe, not closed with the lemma of ss1, as expected
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var sum: int;
  N := *;
  assume 0 < N;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 2];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] + sum];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  assert sum == N * (N + 2);
}

// remaining goals of -teq -simplify:
// goal forall N₅: int :: 0 < N₅ <= 536870911 ==> 2 * N₅ + N₅ * N₅ == 0
