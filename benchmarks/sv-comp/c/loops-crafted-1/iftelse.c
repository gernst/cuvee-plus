// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/iftelse.c
// SV-COMP loops-crafted-1/iftelse.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/iftelse.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
    if (i % 2 != 0) {
      j = j + 3;
    } else {
      k = k + 3;
    }
    if (n > 0) {
      assert(i / 2 <= j);
    }
  }
  result = 0;
  return result;
}

