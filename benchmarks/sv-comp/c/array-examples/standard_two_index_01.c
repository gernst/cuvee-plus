// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_two_index_01.c
// SV-COMP array-examples/standard_two_index_01.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_two_index_01.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int b[];
  int i;
  int j;
  int tmp;
  __VERIFIER_assume(0 < N);
  i = 0;
  j = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    b[i] = tmp;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[j] = b[i];
    i = i + 1;
    j = j + 1;
  }
  i = 0;
  j = 0;
  while (i < N) {
    assert(a[j] == b[j]);
    i = i + 1;
    j = j + 1;
  }
}

