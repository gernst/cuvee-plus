// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/sina3.dfy
// SV-COMP array-fpi/sina3.yml (expected: safe), translated from the C program by hand: a and b
// are set to 1, the sum N of a is added to b into a, which is checked to be N + 1 (sina4, sina5 are variants)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (sina4, sina5 are variants)

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  var b: array<int, int>;
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
    b := b[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := b[i] + sum];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == N + 1;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
