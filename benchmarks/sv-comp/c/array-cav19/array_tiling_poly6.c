// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_tiling_poly6.c
// SV-COMP array-cav19/array_tiling_poly6.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_tiling_poly6.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int S;
  int i;
  int a[];
  S = __VERIFIER_nondet_int();
  __VERIFIER_assume(S > 1);
  i = 0;
  while (i < S) {
    a[i] = (i - 1) * (i + 1);
    i = i + 1;
  }
  i = 0;
  while (i < S) {
    a[i] = a[i] - i * i;
    i = i + 1;
  }
  i = 0;
  while (i < S) {
    assert(a[i] == -1);
    i = i + 1;
  }
}

