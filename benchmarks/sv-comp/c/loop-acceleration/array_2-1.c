// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/array_2-1.c
// SV-COMP loop-acceleration/array_2-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/array_2-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int tmp_2;
  int A[];
  int B[];
  int i;
  int tmp;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    A[i] = tmp_1;
    tmp_2 = __VERIFIER_nondet_int();
    B[i] = tmp_2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    tmp = A[i];
    B[i] = tmp;
    i = i + 1;
  }
  assert(A[N - 1] != B[N - 1]);
}

