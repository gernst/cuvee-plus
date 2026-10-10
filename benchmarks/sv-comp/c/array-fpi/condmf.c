// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/condmf.c
// SV-COMP array-fpi/condmf.yml, translated from benchmarks/sv-comp/dafny/array-fpi/condmf.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int N;

int main(void) {
  int result;
  int i;
  int a[];
  N = __VERIFIER_nondet_int();
  if (N <= 0) {
    result = 1;
    return result;
  }
  i = 0;
  while (i < N) {
    a[i] = 0;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (N % 2 == 1) {
      a[i] = a[i] + 2;
    } else {
      a[i] = a[i] + 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    assert(a[i] % 2 == N % 2);
    i = i + 1;
  }
  result = 1;
  return result;
}

