// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/brs2f.c
// SV-COMP array-fpi/brs2f.yml, translated from benchmarks/sv-comp/dafny/array-fpi/brs2f.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int main(void) {
  int result;
  int i;
  int sum[];
  int a[];
  N = __VERIFIER_nondet_int();
  if (N <= 0) {
    result = 1;
    return result;
  }
  i = 0;
  while (i < N) {
    if (i % 2 == 0) {
      a[i] = 20;
    } else {
      a[i] = 0;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i == 0) {
      sum[0] = 0;
    } else {
      sum[0] = sum[0] + a[i];
    }
    i = i + 1;
  }
  assert(sum[0] <= 2 * N);
  result = 1;
  return result;
}

