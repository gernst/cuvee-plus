// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/sqmf.c
// SV-COMP array-fpi/sqmf.yml, translated from benchmarks/sv-comp/dafny/array-fpi/sqmf.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int main(void) {
  int result;
  int i;
  int a[];
  int b[];
  N = __VERIFIER_nondet_int();
  if (N <= 0) {
    result = 1;
    return result;
  }
  b[0] = 0;
  a[0] = 0;
  i = 1;
  while (i < N) {
    b[i] = b[i - 1] + 2;
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    a[i] = a[i - 1] + b[i - 1] + 2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] == (i + 1) * (i + 1));
    i = i + 1;
  }
  result = 1;
  return result;
}

