// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loops-crafted-1/sum_by_3.c
// SV-COMP loops-crafted-1/sum_by_3.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/sum_by_3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int n;
  int i;
  int k;
  int j;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
  i = 0;
  while (i < n) {
    i = i + 1;
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

