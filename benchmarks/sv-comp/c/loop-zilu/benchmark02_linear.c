// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark02_linear.c
// SV-COMP loop-zilu/benchmark02_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark02_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
  while (i < n) {
    i = i + 1;
  }
  assert(l >= 1);
  result = 0;
  return result;
}

