// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_init5_ground-2.c
// SV-COMP array-examples/standard_init5_ground-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_init5_ground-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int a[];
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
    a[i] = 43;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = 44;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = 45;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = 46;
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    assert(a[x] == 45);
    x = x + 1;
  }
  result = 0;
  return result;
}

