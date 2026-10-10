// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-industry-pattern/mod3.c
// SV-COMP loop-industry-pattern/mod3.yml, translated from benchmarks/sv-comp/dafny/loop-industry-pattern/mod3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int y;
  int b;
  x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x >= 0);
  y = 1;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    if (x % 3 == 1) {
      x = x + 2;
      y = 0;
    } else {
      if (x % 3 == 2) {
        x = x + 1;
        y = 0;
      } else {
        b = __VERIFIER_nondet_int();
        if (b != 0) {
          x = x + 4;
          y = 1;
        } else {
          x = x + 5;
          y = 1;
        }
      }
    }
    b = __VERIFIER_nondet_int();
  }
  if (y == 0) {
    assert(x % 3 == 0);
  }
}

