// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/ss2f.c
// SV-COMP array-fpi/ss2f.yml, translated from benchmarks/sv-comp/dafny/array-fpi/ss2f.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
    a[i] = 2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum[0] = sum[0] + a[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = 0;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] + sum[0];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum[0] = sum[0] + a[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] + sum[0];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == N * (N + 2));
    i = i + 1;
  }
  result = 1;
  return result;
}

