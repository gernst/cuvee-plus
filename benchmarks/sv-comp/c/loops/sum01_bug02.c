// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/sum01_bug02.c
// SV-COMP loops/sum01_bug02.yml, translated from benchmarks/sv-comp/dafny/loops/sum01_bug02.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int j;
  int n;
  int sn;
  j = 10;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  n = tmp_1;
  sn = 0;
  if (n == 2147483647) {
    result = 0;
    return result;
  }
  i = 1;
  while (i <= n) {
    if (i < j) {
      sn = sn + 2;
    }
    j = j - 1;
    i = i + 1;
  }
  assert(sn == n * 2 || sn == 0);
}

