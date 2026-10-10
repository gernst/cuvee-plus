// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invariants/odd.c
// SV-COMP loop-invariants/odd.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/odd.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int b;
  x = 1;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    x = x + 2;
    b = __VERIFIER_nondet_int();
  }
  assert(x % 2 == 1);
}

