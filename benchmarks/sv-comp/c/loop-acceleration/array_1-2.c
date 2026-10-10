// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/array_1-2.c
// SV-COMP loop-acceleration/array_1-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/array_1-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int A[];
  int i;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    A[i] = i;
    i = i + 1;
  }
  assert(A[N - 1] == N - 1);
}

