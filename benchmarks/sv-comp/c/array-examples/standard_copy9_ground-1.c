// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_copy9_ground-1.c
// SV-COMP array-examples/standard_copy9_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_copy9_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a0[];
  int a1[];
  int a2[];
  int a3[];
  int a4[];
  int a5[];
  int a6[];
  int a7[];
  int a8[];
  int a9[];
  int a;
  int i;
  int x;
  int tmp;
  __VERIFIER_assume(0 < N);
  a = 0;
  while (a < N) {
    tmp = __VERIFIER_nondet_int();
    a1[a] = tmp;
    tmp = __VERIFIER_nondet_int();
    a9[a] = tmp;
    a = a + 1;
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
  i = 0;
  while (i < N) {
    a5[i] = a4[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a6[i] = a5[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a7[i] = a6[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a8[i] = a7[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a0[i] = a8[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a0[i] = a9[i];
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(a1[x] == a0[x]);
    x = x + 1;
  }
}

