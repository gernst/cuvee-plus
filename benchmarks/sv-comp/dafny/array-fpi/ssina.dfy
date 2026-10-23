// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-fpi/ssina.dfy
// SV-COMP array-fpi/ssina.yml (expected: safe), translated from the C program by hand: a is set
// to 1, its sum N added to each element, and the new sum N * (N + 1) added again, which gives (N + 1) * (N + 1)
//
// findings: the sum over the array after stores of constants at the counter is read at another counter with the
// same definition, which the lemma of teq.dfy for reads of stores at the same keys does not match, since the keys
// are compared literally; selects_stores_counter of teq.dfy, for counters with the
// same definition, matched through the definitions, closes it (no
// output)
// note: its lemma is part of teq.dfy now (selects_stores_counter) and is removed here

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  N := *;
  assume 0 < N;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 1];
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
  sum := 0;
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
    assert a[i] == (N + 1) * (N + 1);
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
