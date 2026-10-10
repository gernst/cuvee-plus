// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_find_ground-1.c
// SV-COMP array-examples/standard_find_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_find_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int e;
  int i;
  int j;
  int x;
  int tmp;
  __VERIFIER_assume(0 < N);
  e = __VERIFIER_nondet_int();
  i = 0;
  j = 0;
  while (j < N) {
    tmp = __VERIFIER_nondet_int();
    a[j] = tmp;
    j = j + 1;
  }
  while (i < N && a[i] != e) {
    i = i + 1;
  }
  x = 0;
  while (x < i) {
    assert(a[x] != e);
    x = x + 1;
  }
}

