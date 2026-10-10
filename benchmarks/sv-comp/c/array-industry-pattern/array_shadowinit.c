// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-industry-pattern/array_shadowinit.c
// SV-COMP array-industry-pattern/array_shadowinit.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_shadowinit.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int i;
  int k;
  N = __VERIFIER_nondet_int();
  if (N > 0) {
    i = 0;
    k = 0;
    while (i < N) {
      a[k] = k;
      i = i + 1;
      k = k + 1;
    }
    i = 0;
    while (i < N) {
      assert(a[i] == i);
      i = i + 1;
    }
  }
}

