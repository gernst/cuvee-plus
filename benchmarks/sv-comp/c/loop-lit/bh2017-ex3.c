// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/bh2017-ex3.c
// SV-COMP loop-lit/bh2017-ex3.yml, translated from benchmarks/sv-comp/dafny/loop-lit/bh2017-ex3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  _Bool tmp_1;
  _Bool tmp_2;
  _Bool tmp_3;
  int m;
  int n;
  m = 0;
  n = 0;
  while (1 != 0) {
    assert(m <= 60);
    assert(n <= 60);
    tmp_1 = __VERIFIER_nondet_bool();
    if (tmp_1) {
      tmp_2 = __VERIFIER_nondet_bool();
      if (tmp_2) {
        if (m < 60) {
          m = m + 1;
        } else {
          assert(m == 60);
          m = 0;
        }
      }
    } else {
      tmp_3 = __VERIFIER_nondet_bool();
      if (tmp_3) {
        if (n < 60) {
          n = n + 1;
        } else {
          assert(n == 60);
          n = 0;
        }
      }
    }
  }
  result = 0;
  return result;
}

