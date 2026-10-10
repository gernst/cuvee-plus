// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-industry-pattern/array_mul_init.c
// SV-COMP array-industry-pattern/array_mul_init.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_mul_init.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int b[];
  int k;
  int i;
  int c;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    a[i] = i;
    b[i] = i;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    c = __VERIFIER_nondet_int();
    if (c != 0) {
      k = __VERIFIER_nondet_int();
      a[i] = k;
      b[i] = k * k;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == b[i] || b[i] == a[i] * a[i]);
    i = i + 1;
  }
}

