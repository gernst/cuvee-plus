// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/simple_3-1.c
// SV-COMP loop-acceleration/simple_3-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_3-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int x;
  int N;
  x = 0;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  N = tmp_1;
  while (x < N) {
    x = x + 2;
  }
  assert(x % 2 != 0);
}

