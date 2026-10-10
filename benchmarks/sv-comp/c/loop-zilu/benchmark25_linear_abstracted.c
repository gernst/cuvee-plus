// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark25_linear_abstracted.c
// SV-COMP loop-zilu/benchmark25_linear_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark25_linear_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int x;
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  if (!(x < 0)) {
    result = 0;
    return result;
  }
  if (x < 10) {
    x = __VERIFIER_nondet_int();
    if (!(x < 10)) {
      __VERIFIER_assume(false);
    }
    if (x < 10) {
      x = x + 1;
    }
    if (x < 10) {
      __VERIFIER_assume(false);
    }
  }
  assert(x == 10);
  result = 0;
  return result;
}

