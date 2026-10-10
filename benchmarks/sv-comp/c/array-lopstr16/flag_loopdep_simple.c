// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/flag_loopdep_simple.c
// SV-COMP array-lopstr16/flag_loopdep_simple.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/flag_loopdep_simple.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int v;
  int flag;
  int a[];
  __VERIFIER_assume(0 < N);
  flag = 0;
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    a[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] != 0) {
      flag = 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (flag == 0) {
      assert(a[i] == 0);
    }
    i = i + 1;
  }
}

