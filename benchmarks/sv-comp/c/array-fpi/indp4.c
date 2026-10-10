// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/indp4.c
// SV-COMP array-fpi/indp4.yml, translated from benchmarks/sv-comp/dafny/array-fpi/indp4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
    a[i] = (i + 1) * (i + 1);
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
    assert(a[i] == i * i + 1);
    i = i + 1;
  }
  result = 1;
  return result;
}

