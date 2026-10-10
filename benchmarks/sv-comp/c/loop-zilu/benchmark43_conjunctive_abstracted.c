// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark43_conjunctive_abstracted.c
// SV-COMP loop-zilu/benchmark43_conjunctive_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark43_conjunctive_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
  if (!(x < 100 && y < 100)) {
    result = 0;
    return result;
  }
  if (((y < 100 ? 1 : 0) & (x < 100 ? 1 : 0)) != 0) {
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    if (!(((y < 100 ? 1 : 0) & (x < 100 ? 1 : 0)) != 0)) {
      __VERIFIER_assume(false);
    }
    if (x < 100 && y < 100) {
      x = x + 1;
      y = y + 1;
    }
    if (((y < 100 ? 1 : 0) & (x < 100 ? 1 : 0)) != 0) {
      __VERIFIER_assume(false);
    }
  }
  assert(x == 100 || y == 100);
  result = 0;
  return result;
}

