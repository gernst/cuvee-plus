// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/bh2017-ex-add.c
// SV-COMP loop-lit/bh2017-ex-add.yml, translated from benchmarks/sv-comp/dafny/loop-lit/bh2017-ex-add.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int m;
  int n;
  int b;
  int c;
  m = 0;
  n = 0;
  while (true) {
    assert(m <= 60);
    assert(n <= 60);
    b = __VERIFIER_nondet_int();
    c = __VERIFIER_nondet_int();
    if (b != 0 && c != 0) {
      if (m < 60) {
        m = m + 1;
      } else {
        assert(m == 60);
        m = 0;
      }
    }
    b = __VERIFIER_nondet_int();
    c = __VERIFIER_nondet_int();
    if (b != 0 && c != 0) {
      if (n < 60) {
        n = n + 1;
      } else {
        assert(n == 60);
        n = 0;
      }
    }
  }
}

