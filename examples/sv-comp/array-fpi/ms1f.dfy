// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/ms1f.dfy
// SV-COMP array-fpi/ms1f.yml (expected: unsafe), translated from the C program by hand: the
// unsafe variant of ms1, which asserts that the sum, which is 0, is N
//
// findings: unsafe, not closed with the lemmas of ms1, as expected
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
    a := a[i := i % 1];
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
  assert sum == N;
}

// remaining goals of -teq -simplify:
// goal forall N₅: int :: !(0 < N₅ <= 536870911)
