// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/invert_string-3.c
// SV-COMP loops/invert_string-3.yml, translated from benchmarks/sv-comp/dafny/loops/invert_string-3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int max;
  int str1[];
  int str2[];
  int i;
  int j;
  max = 5;
  i = 0;
  while (i < max) {
    tmp_1 = __VERIFIER_nondet_int();
    str1[i] = tmp_1;
    i = i + 1;
  }
  str1[max - 1] = 0;
  j = 0;
  i = max - 1;
  while (i >= 0) {
    str2[j] = str1[i];
    j = j + 1;
    i = i - 1;
  }
  j = max - 1;
  i = 0;
  while (i < max) {
    assert(str1[i] == str2[j]);
    j = j - 1;
    i = i + 1;
  }
}

