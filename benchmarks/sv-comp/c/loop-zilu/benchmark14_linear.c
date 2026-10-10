// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark14_linear.c
// SV-COMP loop-zilu/benchmark14_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark14_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  tmp_1 = __VERIFIER_nondet_int();
  i = tmp_1;
  if (!(i >= 0)) {
    result = 0;
    return result;
  }
  while (i > 0) {
    i = i - 1;
  }
  assert(i >= 0);
  result = 0;
  return result;
}

