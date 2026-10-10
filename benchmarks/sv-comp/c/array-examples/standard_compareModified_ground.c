// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-examples/standard_compareModified_ground.c
// SV-COMP array-examples/standard_compareModified_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_compareModified_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int x;
  int v;
  int rv;
  int a[];
  int b[];
  int c[];
  __VERIFIER_assume(0 < N);
  i = 0;
  rv = 1;
  j = 0;
  while (j < N) {
    v = __VERIFIER_nondet_int();
    a[j] = v;
    v = __VERIFIER_nondet_int();
    b[j] = v;
    j = j + 1;
  }
  while (i < N) {
    if (a[i] != b[i]) {
      rv = 0;
    }
    c[i] = a[i];
    i = i + 1;
  }
  if (rv != 0) {
    x = 0;
    while (x < N) {
      assert(a[x] == b[x]);
      x = x + 1;
    }
  }
  x = 0;
  while (x < N) {
    assert(a[x] == c[x]);
    x = x + 1;
  }
}

