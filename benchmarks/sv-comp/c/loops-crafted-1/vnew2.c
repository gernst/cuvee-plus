// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/vnew2.c
// SV-COMP loops-crafted-1/vnew2.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/vnew2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int n;
  int i;
  int k;
  int j;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
  k = 0;
  j = k;
  i = j;
  while (i < n) {
    i = i + 3;
    j = j + 3;
    k = k + 3;
  }
  if (n > 0) {
    assert(i == j && j == k && i % (n + 3) != 0);
  }
  result = 0;
  return result;
}

