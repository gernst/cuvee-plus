// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invariants/bin-suffix-5.c
// SV-COMP loop-invariants/bin-suffix-5.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/bin-suffix-5.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int b;
  x = 5;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    x = x + 8;
    b = __VERIFIER_nondet_int();
  }
  assert(x % 8 == 5);
}

