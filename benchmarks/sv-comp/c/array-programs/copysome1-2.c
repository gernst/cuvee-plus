// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-programs/copysome1-2.c
// SV-COMP array-programs/copysome1-2.yml, translated from benchmarks/sv-comp/dafny/array-programs/copysome1-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a1[];
  int a2[];
  int i;
  int z;
  int x;
  int tmp;
  __VERIFIER_assume(0 < N);
  z = 150000;
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    a1[i] = tmp;
    tmp = __VERIFIER_nondet_int();
    a2[i] = tmp;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i != z) {
      a2[i] = a1[i];
    }
    i = i + 1;
  }
  z = 150001;
  x = 0;
  while (x < N) {
    if (x != z) {
      assert(a1[x] == a2[x]);
    }
    x = x + 1;
  }
}

