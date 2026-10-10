// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_copy3_ground-1.c
// SV-COMP array-examples/standard_copy3_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_copy3_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int x;
  int v;
  int a1[];
  int a2[];
  int a3[];
  int a4[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    a1[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a2[i] = a1[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a3[i] = a2[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a4[i] = a3[i];
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(a1[x] == a4[x]);
    x = x + 1;
  }
}

