// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/jm2006_variant.c
// SV-COMP loop-lit/jm2006_variant.yml, translated from benchmarks/sv-comp/dafny/loop-lit/jm2006_variant.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int j;
  int x;
  int y;
  int z;
  i = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  if (!(i >= 0)) {
    return;
  }
  if (!(j >= 0)) {
    return;
  }
  x = i;
  y = j;
  z = 0;
  while (x != 0) {
    x = x - 1;
    y = y - 2;
    z = z + 1;
  }
  if (i == j) {
    assert(y == -z);
  }
}

