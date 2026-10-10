// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_sentinel-2.c
// SV-COMP array-examples/standard_sentinel-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_sentinel-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int marker;
  int pos;
  int i;
  int tmp;
  __VERIFIER_assume(0 < N);
  marker = __VERIFIER_nondet_int();
  pos = __VERIFIER_nondet_int();
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    a[i] = tmp;
    i = i + 1;
  }
  if (pos >= 0 && pos < N) {
    a[pos] = marker;
    i = 0;
    while (a[i] != marker) {
      i = i + 1;
    }
    assert(i <= pos);
  }
}

