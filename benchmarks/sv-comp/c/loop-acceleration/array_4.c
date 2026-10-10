// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/array_4.c
// SV-COMP loop-acceleration/array_4.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/array_4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int v;
  int A[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N - 1) {
    v = __VERIFIER_nondet_int();
    A[i] = v;
    i = i + 1;
  }
  A[N - 1] = 0;
  i = 0;
  while (A[i] != 0) {
    i = i + 1;
  }
  assert(i <= N);
}

