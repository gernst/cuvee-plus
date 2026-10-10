// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark26_linear_abstracted.c
// SV-COMP loop-zilu/benchmark26_linear_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark26_linear_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int x;
  int y;
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  y = tmp_2;
  if (!(x < y)) {
    result = 0;
    return result;
  }
  if (x < y) {
    x = __VERIFIER_nondet_int();
    if (!(x < y)) {
      __VERIFIER_assume(false);
    }
    if (x < y) {
      x = x + 1;
    }
    if (x < y) {
      __VERIFIER_assume(false);
    }
  }
  assert(x == y);
  result = 0;
  return result;
}

