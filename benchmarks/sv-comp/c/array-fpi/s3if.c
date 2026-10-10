// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/s3if.c
// SV-COMP array-fpi/s3if.yml, translated from benchmarks/sv-comp/dafny/array-fpi/s3if.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
    a[i] = 3;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] == 3) {
      sum = sum + a[i];
    } else {
      sum = sum * a[i];
    }
    i = i + 1;
  }
  assert(sum == 3 * N);
}

