// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invariants/eq1.c
// SV-COMP loop-invariants/eq1.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/eq1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int w;
  int x;
  int y;
  int z;
  int b;
  int c;
  w = __VERIFIER_nondet_int();
  x = w;
  y = __VERIFIER_nondet_int();
  z = y;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    c = __VERIFIER_nondet_int();
    if (c != 0) {
      w = w + 1;
      x = x + 1;
    } else {
      y = y - 1;
      z = z - 1;
    }
    b = __VERIFIER_nondet_int();
  }
  assert(w == x && y == z);
}

