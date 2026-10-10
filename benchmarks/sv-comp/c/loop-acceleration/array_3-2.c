// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/array_3-2.c
// SV-COMP loop-acceleration/array_3-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/array_3-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int A[];
  int i;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    A[i] = tmp_1;
    i = i + 1;
  }
  i = 0;
  while (i < N && A[i] != 0) {
    i = i + 1;
  }
  assert(i <= 512);
}

