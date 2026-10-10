// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invariants/mod4.c
// SV-COMP loop-invariants/mod4.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/mod4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int b;
  x = 0;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    x = x + 4;
    b = __VERIFIER_nondet_int();
  }
  assert(x % 4 == 0);
}

