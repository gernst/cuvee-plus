// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invariants/const.c
// SV-COMP loop-invariants/const.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/const.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int s;
  int b;
  int c;
  s = 0;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    if (s != 0) {
      s = s + 1;
    }
    c = __VERIFIER_nondet_int();
    if (c != 0) {
      assert(s == 0);
    }
    b = __VERIFIER_nondet_int();
  }
}

