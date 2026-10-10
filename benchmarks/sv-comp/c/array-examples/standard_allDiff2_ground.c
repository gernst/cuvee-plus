// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_allDiff2_ground.c
// SV-COMP array-examples/standard_allDiff2_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_allDiff2_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int a[];
  int i;
  int r;
  int j;
  int x;
  int y;
  __VERIFIER_assume(0 < N);
  r = 1;
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    a[i] = tmp_1;
    i = i + 1;
  }
  i = 1;
  while (i < N && r != 0) {
    j = i - 1;
    while (j >= 0 && r != 0) {
      if (a[i] == a[j]) {
        r = 1;
      }
      j = j - 1;
    }
    i = i + 1;
  }
  if (r != 0) {
    x = 0;
    while (x < N) {
      y = x + 1;
      while (y < N) {
        assert(a[x] != a[y]);
        y = y + 1;
      }
      x = x + 1;
    }
  }
  result = 0;
  return result;
}

