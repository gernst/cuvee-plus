// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/motivex.c
// SV-COMP array-lopstr16/motivex.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/motivex.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int b;
  int k;
  int p[];
  int q[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    p[i] = i;
    q[i] = i;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b = __VERIFIER_nondet_int();
    if (b != 0) {
      k = __VERIFIER_nondet_int();
      p[i] = k;
      q[i] = k * k;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(p[i] == q[i] || q[i] == p[i] * p[i]);
    i = i + 1;
  }
}

