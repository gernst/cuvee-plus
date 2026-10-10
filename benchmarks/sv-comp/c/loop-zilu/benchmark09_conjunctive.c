// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-zilu/benchmark09_conjunctive.c
// SV-COMP loop-zilu/benchmark09_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark09_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int y;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  __VERIFIER_assume(x == y && y >= 0);
  while (x != 0) {
    x = x - 1;
    y = y - 1;
    if (x < 0 || y < 0) {
      break;
    }
  }
  assert(y == 0);
}

