// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark51_polynomial.c
// SV-COMP loop-zilu/benchmark51_polynomial.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark51_polynomial.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int c;
  x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x >= 0 && x <= 50);
  c = __VERIFIER_nondet_int();
  while (c != 0) {
    if (x > 50) {
      x = x + 1;
    }
    if (x == 0) {
      x = x + 1;
    } else {
      x = x - 1;
    }
    c = __VERIFIER_nondet_int();
  }
  assert(x >= 0 && x <= 50);
}

