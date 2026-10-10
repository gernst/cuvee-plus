// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/array_1-1.c
// SV-COMP loop-acceleration/array_1-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/array_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int A[];
  int i;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    A[i] = i;
    i = i + 1;
  }
  assert(A[N - 1] != N - 1);
}

