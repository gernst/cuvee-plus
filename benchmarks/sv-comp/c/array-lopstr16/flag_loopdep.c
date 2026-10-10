// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/flag_loopdep.c
// SV-COMP array-lopstr16/flag_loopdep.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/flag_loopdep.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int flag;
  _Bool a[];
  __VERIFIER_assume(0 < N);
  flag = 0;
  i = 0;
  while (i < N) {
    a[i] = true;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i]) {
      flag = 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (flag == 0) {
      assert(!a[i]);
    }
    i = i + 1;
  }
}

