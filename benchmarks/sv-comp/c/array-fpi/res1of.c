// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/res1of.c
// SV-COMP array-fpi/res1of.yml, translated from benchmarks/sv-comp/dafny/array-fpi/res1of.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int main(void) {
  int result;
  int i;
  int sum[];
  int a[];
  int b[];
  N = __VERIFIER_nondet_int();
  if (N <= 0) {
    result = 1;
    return result;
  }
  sum[0] = 0;
  i = 0;
  while (i < N) {
    a[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum[0] = sum[0] + a[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum[0] = sum[0] + b[i];
    i = i + 1;
  }
  assert(sum[0] <= N);
  result = 1;
  return result;
}

