// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_partial_init_ground.c
// SV-COMP array-examples/standard_partial_init_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_partial_init_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int A[];
  int B[];
  int C[];
  int i;
  int j;
  int x;
  int tmp;
  __VERIFIER_assume(0 < N);
  j = 0;
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    A[i] = tmp;
    tmp = __VERIFIER_nondet_int();
    B[i] = tmp;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (A[i] == B[i]) {
      C[j] = i;
      j = j + 1;
    }
    i = i + 1;
  }
  x = 0;
  while (x < j) {
    assert(C[x] <= x + i - j);
    x = x + 1;
  }
  x = 0;
  while (x < j) {
    assert(C[x] >= x);
    x = x + 1;
  }
}

