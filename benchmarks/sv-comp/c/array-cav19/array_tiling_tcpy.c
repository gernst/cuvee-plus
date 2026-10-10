// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_tiling_tcpy.c
// SV-COMP array-cav19/array_tiling_tcpy.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_tiling_tcpy.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int S;
  int i;
  int a[];
  int acopy[];
  S = __VERIFIER_nondet_int();
  __VERIFIER_assume(S > 1);
  i = 0;
  while (i < S) {
    acopy[2 * S - (i + 1)] = a[2 * S - (i + 1)];
    acopy[i] = a[i];
    i = i + 1;
  }
  i = 0;
  while (i < 2 * S) {
    assert(acopy[i] == a[i]);
    i = i + 1;
  }
}

