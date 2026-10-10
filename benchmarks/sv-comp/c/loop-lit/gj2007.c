// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/gj2007.c
// SV-COMP loop-lit/gj2007.yml, translated from benchmarks/sv-comp/dafny/loop-lit/gj2007.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  int y;
  __VERIFIER_assume(50 <= N);
  x = 0;
  y = 50;
  while (x < N) {
    if (x < 50) {
      x = x + 1;
    } else {
      x = x + 1;
      y = y + 1;
    }
  }
  assert(y == N);
}

