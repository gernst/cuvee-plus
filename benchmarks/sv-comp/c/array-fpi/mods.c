// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/mods.c
// SV-COMP array-fpi/mods.yml, translated from benchmarks/sv-comp/dafny/array-fpi/mods.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int sum;
  int a[];
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < N);
  sum = 0;
  i = 0;
  while (i < N) {
    a[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum = sum + a[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] + sum;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] % (sum + 1);
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == 0);
    i = i + 1;
  }
}

