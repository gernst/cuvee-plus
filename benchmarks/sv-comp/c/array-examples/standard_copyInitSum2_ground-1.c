// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_copyInitSum2_ground-1.c
// SV-COMP array-examples/standard_copyInitSum2_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_copyInitSum2_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int a[];
  int b[];
  int i;
  int x;
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    a[i] = 42;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b[i] = a[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = b[i] + i;
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(b[x] == 42 + x);
    x = x + 1;
  }
  result = 0;
  return result;
}

