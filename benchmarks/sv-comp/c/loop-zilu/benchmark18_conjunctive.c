// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark18_conjunctive.c
// SV-COMP loop-zilu/benchmark18_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark18_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int i;
  int k;
  int n;
  tmp_1 = __VERIFIER_nondet_int();
  i = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  k = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  n = tmp_3;
  if (!(i == 0 && k == 0 && n > 0)) {
    result = 0;
    return result;
  }
  while (i < n) {
    i = i + 1;
    k = k + 1;
  }
  assert(i == k && k == n);
  result = 0;
  return result;
}

