// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-fpi/ss2.dfy
// SV-COMP array-fpi/ss2.yml (expected: safe), translated from the C program by hand: a is set to
// 1 and summed up to N, then set to 0 plus N, the sum is increased by N * N, and added to each element, which gives
// N * (N + 2) (ss3, ss4 are variants)
//
// findings: as ssina, by the lemma for reads of stores at a counter with the same definition; closed (no output)
// (ss3, ss4 are variants)
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
    a := a[i := 0];
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
  i := 0;
  while i < N {
    a := a[i := a[i] + sum];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == N * (N + 2);
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
