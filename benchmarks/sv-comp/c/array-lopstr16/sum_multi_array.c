// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/sum_multi_array.c
// SV-COMP array-lopstr16/sum_multi_array.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/sum_multi_array.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int v;
  int a[];
  int b[];
  int c[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    a[i] = v;
    v = __VERIFIER_nondet_int();
    b[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    c[i] = a[i] + b[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(c[i] == a[i] + b[i]);
    i = i + 1;
  }
}

