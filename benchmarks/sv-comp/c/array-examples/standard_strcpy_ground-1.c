// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_strcpy_ground-1.c
// SV-COMP array-examples/standard_strcpy_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_strcpy_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int x;
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
  x = 0;
  while (x < i) {
    assert(dst[x] == src[x]);
    x = x + 1;
  }
}

