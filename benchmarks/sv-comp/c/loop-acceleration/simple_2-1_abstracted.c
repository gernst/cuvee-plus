// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/simple_2-1_abstracted.c
// SV-COMP loop-acceleration/simple_2-1_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_2-1_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int x;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  x = tmp_1;
  if (x < N) {
    x = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= x);
  }
  if (x < N) {
    __VERIFIER_assume(false);
  }
  assert(x >= N);
}

