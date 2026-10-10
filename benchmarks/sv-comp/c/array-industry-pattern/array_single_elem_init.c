// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-industry-pattern/array_single_elem_init.c
// SV-COMP array-industry-pattern/array_single_elem_init.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_single_elem_init.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int q;
  int a[];
  int b[];
  int c[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    q = __VERIFIER_nondet_int();
    a[i] = 0;
    if (q == 0) {
      a[i] = 1;
      b[i] = i % 2;
    }
    if (a[i] != 0) {
      if (b[i] == 0) {
        c[i] = 0;
      } else {
        c[i] = 1;
      }
    }
    i = i + 1;
  }
  a[15000] = 1;
  i = 0;
  while (i < N) {
    if (i == 15000) {
      assert(c[i] == 0);
    }
    i = i + 1;
  }
}

