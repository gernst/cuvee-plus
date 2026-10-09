// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/array_1-2.dfy
// SV-COMP loop-acceleration/array_1-2.yml (expected: safe), translated from the C program by
// hand: A[i] is set to i for i below 1024, and A[1023] is 1023
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary values that keep the verdict: N for 1024, the assertion on
// A[1023] is on A[N - 1]

method main() {
  var N: int;
  var A: array<int, int>;
  var i: int;
  assume 0 < N;
  i := 0;
  while i < N {
    A := A[i := i];
    i := i + 1;
  }
  assert A[N - 1] == N - 1;
}

// remaining goals of -teq -simplify:
// none
