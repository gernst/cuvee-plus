// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark05_conjunctive.c
// SV-COMP loop-zilu/benchmark05_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark05_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int y;
  int n;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(x >= 0 && x <= y && y < n);
  while (x < n) {
    x = x + 1;
    if (x > y) {
      y = y + 1;
    }
  }
  assert(y == n);
}

