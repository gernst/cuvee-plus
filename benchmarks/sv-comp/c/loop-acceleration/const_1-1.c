// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/const_1-1.c
// SV-COMP loop-acceleration/const_1-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/const_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  int y;
  __VERIFIER_assume(0 < N);
  x = 1;
  y = 0;
  while (y < N) {
    x = 0;
    y = y + 1;
  }
  assert(x == 0);
}

