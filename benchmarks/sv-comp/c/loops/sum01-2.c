// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/sum01-2.c
// SV-COMP loops/sum01-2.yml, translated from benchmarks/sv-comp/dafny/loops/sum01-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int i;
  int n;
  int sn;
  n = __VERIFIER_nondet_int();
  sn = 0;
  i = 1;
  while (i <= n) {
    sn = sn + 2;
    i = i + 1;
  }
  assert(sn == n * 2 || sn == 0);
}

