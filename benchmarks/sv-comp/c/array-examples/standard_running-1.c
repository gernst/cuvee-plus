// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_running-1.c
// SV-COMP array-examples/standard_running-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_running-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int b[];
  int i;
  int f;
  int tmp;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    a[i] = tmp;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] >= 0) {
      b[i] = 1;
    } else {
      b[i] = 0;
    }
    i = i + 1;
  }
  f = 1;
  i = 0;
  while (i < N) {
    if (a[i] >= 0 && b[i] == 0) {
      f = 0;
    }
    if (a[i] < 0 && b[i] == 0) {
      f = 0;
    }
    i = i + 1;
  }
  assert(f != 0);
}

