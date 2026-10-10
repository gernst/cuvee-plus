// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/underapprox_2-2.c
// SV-COMP loop-acceleration/underapprox_2-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/underapprox_2-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  int y;
  __VERIFIER_assume(0 < N);
  x = 0;
  y = 1;
  while (x < N) {
    x = x + 1;
    y = y * 2;
  }
  assert(x == N);
}

