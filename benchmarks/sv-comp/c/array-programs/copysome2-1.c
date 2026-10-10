// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-programs/copysome2-1.c
// SV-COMP array-programs/copysome2-1.yml, translated from benchmarks/sv-comp/dafny/array-programs/copysome2-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int x;
  int z;
  int v;
  int a1[];
  int a2[];
  int a3[];
  __VERIFIER_assume(0 < N);
  z = 150000;
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    a1[i] = v;
    v = __VERIFIER_nondet_int();
    a2[i] = v;
    v = __VERIFIER_nondet_int();
    a3[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i != z) {
      a2[i] = a1[i];
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i != z) {
      a3[i] = a2[i];
    } else {
      a3[i] = a1[i];
    }
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(a1[x] == a3[x]);
    x = x + 1;
  }
}

