// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/sum04-2.c
// SV-COMP loops/sum04-2.yml, translated from benchmarks/sv-comp/dafny/loops/sum04-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int i;
  int sn;
  sn = 0;
  i = 1;
  while (i <= 8) {
    sn = sn + 2;
    i = i + 1;
  }
  assert(sn == 8 * 2 || sn == 0);
}

