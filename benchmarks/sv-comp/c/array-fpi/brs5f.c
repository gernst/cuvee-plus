// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/brs5f.c
// SV-COMP array-fpi/brs5f.yml, translated from benchmarks/sv-comp/dafny/array-fpi/brs5f.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int main(void) {
  int result;
  int check_size;
  int i;
  int sum[];
  int a[];
  N = __VERIFIER_nondet_int();
  if (N <= 0) {
    result = 1;
    return result;
  }
  check_size = 4 > 5 ? 4 : 5;
  i = 0;
  while (i < N) {
    if (i % 5 == 0) {
      a[i] = 5;
    } else {
      a[i] = 5;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i == 0) {
      sum[0] = N + 5;
    } else {
      sum[0] = sum[0] + a[i];
    }
    i = i + 1;
  }
  assert(sum[0] <= 5 * N);
  result = 1;
  return result;
}

