// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-industry-pattern/array_range_init.c
// SV-COMP array-industry-pattern/array_range_init.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_range_init.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    if (i >= 0 && i <= 10000) {
      a[i] = 10;
    } else {
      a[i] = 0;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == 10);
    i = i + 1;
  }
}

