// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/terminator_03-2_abstracted.c
// SV-COMP loops/terminator_03-2_abstracted.yml, translated from benchmarks/sv-comp/dafny/loops/terminator_03-2_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
  if (y > 0) {
    if (x < 100) {
      x = __VERIFIER_nondet_int();
    }
    if (x < 100) {
      __VERIFIER_assume(false);
    }
  }
  assert(y <= 0 || y > 0 && x >= 100);
  result = 0;
  return result;
}

