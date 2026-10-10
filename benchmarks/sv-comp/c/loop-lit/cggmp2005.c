// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/cggmp2005.c
// SV-COMP loop-lit/cggmp2005.yml, translated from benchmarks/sv-comp/dafny/loop-lit/cggmp2005.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int j;
  i = 1;
  j = 10;
  while (j >= i) {
    i = i + 2;
    j = -1 + j;
  }
  assert(j == 6);
}

