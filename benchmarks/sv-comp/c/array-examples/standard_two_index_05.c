// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_two_index_05.c
// SV-COMP array-examples/standard_two_index_05.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_two_index_05.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int a[];
  int b[];
  int i;
  int j;
  __VERIFIER_assume(0 < N);
  i = 0;
  j = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    b[i] = tmp_1;
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    a[j] = b[i];
    i = i + 5;
    j = j + 1;
  }
  i = 1;
  j = 0;
  while (i < N) {
    assert(a[j] == b[5 * j + 1]);
    i = i + 5;
    j = j + 1;
  }
  result = 0;
  return result;
}

