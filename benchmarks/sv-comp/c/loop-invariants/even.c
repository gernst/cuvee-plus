// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invariants/even.c
// SV-COMP loop-invariants/even.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/even.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int b;
  x = 0;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    x = x + 2;
    b = __VERIFIER_nondet_int();
  }
  assert(x % 2 == 0);
}

