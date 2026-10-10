// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/jm2006.c
// SV-COMP loop-lit/jm2006.yml, translated from benchmarks/sv-comp/dafny/loop-lit/jm2006.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int j;
  int x;
  int y;
  i = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  __VERIFIER_assume(i >= 0 && j >= 0);
  x = i;
  y = j;
  while (x != 0) {
    x = x - 1;
    y = y - 1;
  }
  if (i == j) {
    assert(y == 0);
  }
}

