// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/mine2017-ex4.8.c
// SV-COMP loop-lit/mine2017-ex4.8.yml, translated from benchmarks/sv-comp/dafny/loop-lit/mine2017-ex4.8.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  _Bool tmp_1;
  int v;
  v = 0;
  while (true) {
    tmp_1 = __VERIFIER_nondet_bool();
    if ((tmp_1 ? 1 : 0) != 0) {
      break;
    }
    assert(0 <= v);
    assert(v <= 1);
    if (v == 0) {
      v = 1;
    }
  }
  result = 0;
  return result;
}

