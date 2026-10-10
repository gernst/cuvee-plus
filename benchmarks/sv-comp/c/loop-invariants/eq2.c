// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invariants/eq2.c
// SV-COMP loop-invariants/eq2.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/eq2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int w;
  int x;
  int y;
  int z;
  int b;
  w = __VERIFIER_nondet_int();
  x = w;
  y = w + 1;
  z = x + 1;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    y = y + 1;
    z = z + 1;
    b = __VERIFIER_nondet_int();
  }
  assert(y == z);
}

