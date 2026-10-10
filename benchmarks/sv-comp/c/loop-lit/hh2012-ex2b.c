// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/hh2012-ex2b.c
// SV-COMP loop-lit/hh2012-ex2b.yml, translated from benchmarks/sv-comp/dafny/loop-lit/hh2012-ex2b.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  _Bool tmp_1;
  int n;
  n = 0;
  while (1 != 0) {
    assert(n <= 60);
    tmp_1 = __VERIFIER_nondet_bool();
    if (tmp_1) {
      if (n < 60) {
        n = n + 1;
      } else {
        assert(n == 60);
        n = 0;
      }
    }
  }
  result = 0;
  return result;
}

