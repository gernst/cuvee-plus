// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark34_conjunctive.c
// SV-COMP loop-zilu/benchmark34_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark34_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int j;
  int k;
  int n;
  tmp_1 = __VERIFIER_nondet_int();
  j = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  k = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  n = tmp_3;
  if (!(j == 0 && k == n && n > 0)) {
    result = 0;
    return result;
  }
  while (j < n && n > 0) {
    j = j + 1;
    k = k - 1;
  }
  assert(k == 0);
  result = 0;
  return result;
}

