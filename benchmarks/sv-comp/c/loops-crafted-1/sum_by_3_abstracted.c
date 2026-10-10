// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/sum_by_3_abstracted.c
// SV-COMP loops-crafted-1/sum_by_3_abstracted.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/sum_by_3_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int n;
  int i;
  int k;
  int j;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
  i = 0;
  if (i < n) {
    i = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= i);
    if (!(i < n)) {
      __VERIFIER_assume(false);
    }
    if (i < n) {
      i = i + 1;
    }
    if (i < n) {
      __VERIFIER_assume(false);
    }
  }
  j = i;
  while (j < n) {
    j = j + 1;
  }
  k = j;
  while (k < n) {
    k = k + 1;
  }
  assert((i + j + k) / 3 <= n);
  result = 0;
  return result;
}

