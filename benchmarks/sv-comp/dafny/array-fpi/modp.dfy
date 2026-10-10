// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/modp.dfy
// SV-COMP array-fpi/modp.yml (expected: safe), translated from the C program by hand: sum counts
// to N, a is set to it, and a[i] % N == 0 is checked
//
// findings: -teq -simplify reduces the goal to N % N == 0, which mod_self of teq.dfy, the remainder of a
// positive value modulo itself, closes (no output)
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
    sum := sum + 1;
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := sum];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert rem(a[i], N) == 0;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
