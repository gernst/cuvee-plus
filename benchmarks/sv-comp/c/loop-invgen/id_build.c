// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/id_build.c
// SV-COMP loop-invgen/id_build.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/id_build.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int offset;
  int length;
  int nlen;
  int i;
  int j;
  tmp_1 = __VERIFIER_nondet_int();
  nlen = tmp_1;
  i = 0;
  while (i < nlen) {
    j = 0;
    while (j < 8) {
      assert(0 <= nlen - 1 - i);
      assert(nlen - 1 - i < nlen);
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

