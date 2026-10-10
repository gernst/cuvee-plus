// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_strcmp_ground.c
// SV-COMP array-examples/standard_strcmp_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_strcmp_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int x;
  int v;
  int c;
  int a[];
  int b[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    a[i] = v;
    v = __VERIFIER_nondet_int();
    b[i] = v;
    i = i + 1;
  }
  c = 0;
  i = 0;
  while (i < N) {
    if (b[i] != a[i]) {
      c = 1;
      break;
    }
    i = i + 1;
  }
  if (c == 0) {
    x = 0;
    while (x < N) {
      assert(a[x] == b[x]);
      x = x + 1;
    }
  }
}

