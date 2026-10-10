// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark02_linear_abstracted.c
// SV-COMP loop-zilu/benchmark02_linear_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark02_linear_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int n;
  int i;
  int l;
  tmp_1 = __VERIFIER_nondet_int();
  n = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  i = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  l = tmp_3;
  i = l;
  if (!(l > 0)) {
    result = 0;
    return result;
  }
  if (i < n) {
    i = __VERIFIER_nondet_int();
  }
  if (i < n) {
    __VERIFIER_assume(false);
  }
  assert(l >= 1);
  result = 0;
  return result;
}

