// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/brs1f.dfy
// SV-COMP array-fpi/brs1f.yml (expected: unsafe), translated from the C program by hand: the
// unsafe variant of brs1, whose sum starts at N / 2 + 10 in the first iteration, such that it exceeds N
//
// findings: unsafe, not closed with the lemmas of brs1, as expected
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
      sum := N / 2 + 10;
    } else {
      sum := sum + a[i];
    }
    i := i + 1;
  }
  assert sum <= N;
}

// remaining goals of -teq -simplify:
// goal forall N₅: int :: 0 < N₅ <= 536870911 ==> N₅ / 2 + 9 <= 0
