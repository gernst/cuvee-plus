// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/modp.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/modp.yml (expected: safe), translated from the C program by hand: sum counts
// to N, a is set to it, and a[i] % N == 0 is checked
//
// findings: -teq -simplify reduces the goal to N % N == 0, which a lemma for the remainder of a nonzero value
// modulo itself closes (no output)

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
    assert a[i] % N == 0;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
