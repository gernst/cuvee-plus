// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/indp5f.c
// SV-COMP array-fpi/indp5f.yml, translated from benchmarks/sv-comp/dafny/array-fpi/indp5f.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int main(void) {
  int result;
  int i;
  int a[];
  int sum[];
  N = __VERIFIER_nondet_int();
  if (N <= 0) {
    result = 1;
    return result;
  }
  sum[0] = 1;
  i = 0;
  while (i < N) {
    a[i] = (i + 1) * (i + 1);
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] - i * i;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] - i;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] - i;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum[0] = sum[0] + a[i];
    i = i + 1;
  }
  assert(sum[0] == N);
  result = 1;
  return result;
}

