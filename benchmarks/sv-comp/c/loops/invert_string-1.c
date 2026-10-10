// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/invert_string-1.c
// SV-COMP loops/invert_string-1.yml, translated from benchmarks/sv-comp/dafny/loops/invert_string-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int MAX;
  int str1[];
  int str2[];
  int cont;
  int i;
  int j;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  MAX = tmp_1;
  if (!(MAX > 0)) {
    __VERIFIER_assume(false);
  }
  cont = 0;
  i = 0;
  while (i < MAX) {
    tmp_2 = __VERIFIER_nondet_int();
    str1[i] = tmp_2;
    i = i + 1;
  }
  str1[MAX - 1] = 0;
  j = 0;
  i = MAX - 1;
  while (i >= 0) {
    str2[j] = str1[0];
    j = j + 1;
    i = i - 1;
  }
  j = MAX - 1;
  i = 0;
  while (i < MAX) {
    assert(str1[i] == str2[j]);
    j = j - 1;
    i = i + 1;
  }
}

