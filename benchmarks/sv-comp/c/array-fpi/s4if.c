// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/s4if.c
// SV-COMP array-fpi/s4if.yml, translated from benchmarks/sv-comp/dafny/array-fpi/s4if.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
  sum[0] = 0;
  i = 0;
  while (i < N) {
    a[i] = 4;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] == 4) {
      sum[0] = sum[0] + a[i];
    } else {
      sum[0] = sum[0] * a[i];
    }
    i = i + 1;
  }
  assert(sum[0] == 4 * N);
  result = 1;
  return result;
}

