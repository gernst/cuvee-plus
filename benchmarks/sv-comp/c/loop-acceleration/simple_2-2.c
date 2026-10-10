// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/simple_2-2.c
// SV-COMP loop-acceleration/simple_2-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_2-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int x;
  __VERIFIER_assume(0 < N);
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  x = tmp_1;
  while (x < N) {
    x = x + 1;
  }
  assert(x > N);
}

