// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/base_case.c
// SV-COMP array-lopstr16/base_case.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/base_case.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int x;
  int n[];
  _Bool p[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    x = __VERIFIER_nondet_int();
    n[i] = x;
    if (x == 0) {
      p[i] = true;
    } else {
      p[i] = false;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (n[i] == 0) {
      assert(p[i]);
    }
    i = i + 1;
  }
}

