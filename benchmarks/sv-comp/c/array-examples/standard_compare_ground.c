// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-examples/standard_compare_ground.c
// SV-COMP array-examples/standard_compare_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_compare_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int b[];
  int i;
  int rv;
  int x;
  int tmp;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    a[i] = tmp;
    tmp = __VERIFIER_nondet_int();
    b[i] = tmp;
    i = i + 1;
  }
  i = 0;
  rv = 1;
  while (i < N) {
    if (a[i] != b[i]) {
      rv = 0;
    }
    i = i + 1;
  }
  if (rv != 0) {
    x = 0;
    while (x < N) {
      assert(a[x] == b[x]);
      x = x + 1;
    }
  }
}

