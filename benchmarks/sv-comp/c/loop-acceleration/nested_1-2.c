// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/nested_1-2.c
// SV-COMP loop-acceleration/nested_1-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/nested_1-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int M;
  int L;
  int x;
  int y;
  __VERIFIER_assume(0 < M);
  __VERIFIER_assume(0 < L);
  x = 0;
  y = 0;
  while (x < M) {
    y = 0;
    while (y < L) {
      y = y + 1;
    }
    x = x + 1;
  }
  assert(x % 2 == 0);
}

