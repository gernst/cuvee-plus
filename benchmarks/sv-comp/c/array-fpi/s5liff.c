// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/s5liff.c
// SV-COMP array-fpi/s5liff.yml, translated from benchmarks/sv-comp/dafny/array-fpi/s5liff.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
  check_size = 4 > 6 ? 4 : 6;
  sum[0] = N;
  i = 0;
  while (i < N) {
    a[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] == 1) {
      a[i] = a[i] + 5;
    } else {
      a[i] = a[i] - 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum[0] = sum[0] + a[i];
    i = i + 1;
  }
  assert(sum[0] == 6 * N);
  result = 1;
  return result;
}

