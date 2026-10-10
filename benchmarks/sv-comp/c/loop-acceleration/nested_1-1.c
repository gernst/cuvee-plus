// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/nested_1-1.c
// SV-COMP loop-acceleration/nested_1-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/nested_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int M;
  int x;
  int y;
  __VERIFIER_assume(0 < N && N % 2 == 1);
  __VERIFIER_assume(0 < M);
  x = 0;
  y = 0;
  while (x < N) {
    y = 0;
    while (y < M) {
      y = y + 1;
    }
    x = x + 1;
  }
  assert(x % 2 != 0);
}

