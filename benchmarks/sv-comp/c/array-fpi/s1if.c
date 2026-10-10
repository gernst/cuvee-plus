// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/s1if.c
// SV-COMP array-fpi/s1if.yml, translated from benchmarks/sv-comp/dafny/array-fpi/s1if.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a[];
  int sum;
  int i;
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
    if (a[i] == 1) {
      sum = sum + a[i];
    } else {
      sum = sum * a[i];
    }
    i = i + 1;
  }
  assert(sum == N);
}

