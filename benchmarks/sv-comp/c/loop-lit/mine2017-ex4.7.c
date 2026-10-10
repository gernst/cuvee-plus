// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/mine2017-ex4.7.c
// SV-COMP loop-lit/mine2017-ex4.7.yml, translated from benchmarks/sv-comp/dafny/loop-lit/mine2017-ex4.7.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  _Bool tmp_1;
  _Bool tmp_2;
  int x;
  x = 0;
  while (true) {
    tmp_1 = __VERIFIER_nondet_bool();
    if ((tmp_1 ? 1 : 0) != 0) {
      break;
    }
    assert(0 <= x);
    assert(x <= 40);
    tmp_2 = __VERIFIER_nondet_bool();
    if ((tmp_2 ? 1 : 0) == 0) {
      x = x + 1;
      if (x > 40) {
        x = 0;
      }
    }
  }
  result = 0;
  return result;
}

