// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/sum_array-2-2.c
// SV-COMP loops/sum_array-2-2.yml, translated from benchmarks/sv-comp/dafny/loops/sum_array-2-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int M;
  int A[];
  int B[];
  int C[];
  int i;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  M = tmp_1;
  if (M > 1000000) {
    result = 0;
    return result;
  }
  i = 0;
  while (i < M) {
    tmp_2 = __VERIFIER_nondet_int();
    A[i] = tmp_2;
    i = i + 1;
  }
  i = 0;
  while (i < M) {
    tmp_3 = __VERIFIER_nondet_int();
    B[i] = tmp_3;
    i = i + 1;
  }
  i = 0;
  while (i < M) {
    C[i] = A[i] + B[i];
    i = i + 1;
  }
  i = 0;
  while (i < M) {
    assert(C[i] == A[i] + B[i]);
    i = i + 1;
  }
}

