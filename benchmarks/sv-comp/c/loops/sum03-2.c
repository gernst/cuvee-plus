// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/sum03-2.c
// SV-COMP loops/sum03-2.yml, translated from benchmarks/sv-comp/dafny/loops/sum03-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int sn;
  int loop1;
  int n1;
  int x;
  sn = 0;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  loop1 = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_2);
  n1 = tmp_2;
  x = 0;
  while (1 != 0) {
    sn = sn + 2;
    x = x + 1;
    assert(sn == x * 2 || sn == 0);
  }
}

