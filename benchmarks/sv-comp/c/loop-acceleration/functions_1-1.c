// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/functions_1-1.c
// SV-COMP loop-acceleration/functions_1-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/functions_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  __VERIFIER_assume(0 < N);
  x = 0;
  while (x < N) {
    x = x + 2;
  }
  assert(x % 2 == 0);
}

