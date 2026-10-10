// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark33_linear.c
// SV-COMP loop-zilu/benchmark33_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark33_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  __VERIFIER_assume(0 < N);
  x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x >= 0);
  while (x < N && x >= 0) {
    x = x + 1;
  }
  assert(x >= N);
}

