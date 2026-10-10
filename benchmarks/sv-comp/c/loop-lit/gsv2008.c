// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/gsv2008.c
// SV-COMP loop-lit/gsv2008.yml, translated from benchmarks/sv-comp/dafny/loop-lit/gsv2008.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int y;
  x = -50;
  y = __VERIFIER_nondet_int();
  while (x < 0) {
    x = x + y;
    y = y + 1;
  }
  assert(y > 0);
}

