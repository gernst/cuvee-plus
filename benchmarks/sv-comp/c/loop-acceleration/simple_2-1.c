// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/simple_2-1.c
// SV-COMP loop-acceleration/simple_2-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_2-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  __VERIFIER_assume(0 < N);
  x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x >= 0);
  while (x < N) {
    x = x + 1;
  }
  assert(x >= N);
}

