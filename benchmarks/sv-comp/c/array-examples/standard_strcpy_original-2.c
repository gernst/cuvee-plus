// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_strcpy_original-2.c
// SV-COMP array-examples/standard_strcpy_original-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_strcpy_original-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int v;
  int src[];
  int dst[];
  __VERIFIER_assume(0 < N);
  i = 0;
  j = 0;
  while (j < N) {
    v = __VERIFIER_nondet_int();
    src[j] = v;
    j = j + 1;
  }
  while (i < N && src[i] != 0) {
    dst[i] = src[i];
    i = i + 1;
  }
  i = 0;
  while (i < N && src[i] != 0) {
    assert(dst[i] == src[i]);
    i = i + 1;
  }
}

