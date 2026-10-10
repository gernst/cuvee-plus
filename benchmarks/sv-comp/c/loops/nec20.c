// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/nec20.c
// SV-COMP loops/nec20.yml, translated from benchmarks/sv-comp/dafny/loops/nec20.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int b;

int main(void) {
  int result;
  int N;
  _Bool tmp_1;
  _Bool k;
  int i;
  int n;
  int j;
  int a[];
  __VERIFIER_assume(1 < N);
  tmp_1 = __VERIFIER_nondet_bool();
  k = tmp_1;
  if (k) {
    n = 0;
  } else {
    n = N - 1;
  }
  i = 0;
  j = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= j);
  while (i <= n) {
    i = i + 1;
    j = j + 2;
  }
  a[i] = 0;
  assert(j < N + 1);
  a[j] = 0;
  a[b] = 0;
  if (b >= 0 && b < N - 1) {
    a[b] = 1;
  } else {
    a[b % (N - 1)] = 1;
  }
  result = 1;
  return result;
}

