// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/mods.dfy
// SV-COMP array-fpi/mods.yml (expected: safe), translated from the C program by hand: a is set
// to 1, summed up to N, N is added to each element, which is then taken modulo N + 1, and checked to be 0
//
// findings: as modp, (N + 1) % (N + 1) == 0, by the same lemma; closed (no output)
// note: its lemma is part of teq.dfy now (mod_self) and is removed here

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
  i := 0;
  while i < N {
    a := a[i := rem(a[i], sum + 1)];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == 0;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
