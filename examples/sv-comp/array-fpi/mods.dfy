// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/mods.dfy
// SV-COMP array-fpi/mods.yml (expected: safe), translated from the C program by hand: a is set
// to 1, summed up to N, N is added to each element, which is then taken modulo N + 1, and checked to be 0
//
// findings: as modp, (N + 1) % (N + 1) == 0, by the same lemma; closed (no output)

// the remainder of a nonzero value modulo itself (not about traces)
lemma {:rw} {:teq} lemma_1(x: int)
  requires x != 0
  ensures x % x == 0

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  N := *;
  assume 0 < N <= 536870911;
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
    a := a[i := a[i] % (sum + 1)];
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
