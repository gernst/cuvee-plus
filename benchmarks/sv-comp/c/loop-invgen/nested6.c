// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/nested6.c
// SV-COMP loop-invgen/nested6.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/nested6.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int j;
  int k;
  int n;
  k = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  if (k == n) {} else {
    result = 0;
    return result;
  }
  i = 0;
  while (i < n) {
    j = 2 * i;
    while (j < n) {
      tmp_1 = __VERIFIER_nondet_int();
      if (tmp_1 != 0) {
        k = j;
        while (k < n) {
          assert(k >= 2 * i);
          k = k + 1;
        }
      } else {
        assert(k >= n);
        assert(k <= n);
      }
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

