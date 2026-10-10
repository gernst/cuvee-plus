// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_vararg_ground.c
// SV-COMP array-examples/standard_vararg_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_vararg_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int a;
  int x;
  int v;
  int aa[];
  __VERIFIER_assume(0 < N);
  a = 0;
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    aa[i] = v;
    i = i + 1;
  }
  while (aa[a] >= 0) {
    a = a + 1;
  }
  x = 0;
  while (x < a) {
    assert(aa[x] >= 0);
    x = x + 1;
  }
}

