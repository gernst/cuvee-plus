// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/nested9.c
// SV-COMP loop-invgen/nested9.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/nested9.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int __BLAST_NONDET;

int main(void) {
  int result;
  int i;
  int j;
  int k;
  int n;
  int l;
  int m;
  n = __VERIFIER_nondet_int();
  m = __VERIFIER_nondet_int();
  l = __VERIFIER_nondet_int();
  if (3 * n <= m + l) {} else {
    result = 0;
    return result;
  }
  i = 0;
  while (i < n) {
    j = 2 * i;
    while (j < 3 * i) {
      k = i;
      while (k < j) {
        assert(k - i <= 2 * n);
        k = k + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

