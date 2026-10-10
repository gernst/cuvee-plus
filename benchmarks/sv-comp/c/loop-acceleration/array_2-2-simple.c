// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/array_2-2-simple.c
// SV-COMP loop-acceleration/array_2-2-simple.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/array_2-2-simple.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int A[];
  int B[];
  int i;
  int tmp;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    tmp = A[i];
    B[i] = tmp;
    i = i + 1;
  }
  assert(A[N / 2] == B[N / 2]);
}

