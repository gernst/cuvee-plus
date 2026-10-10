// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/ddlm2013.c
// SV-COMP loop-lit/ddlm2013.yml, translated from benchmarks/sv-comp/dafny/loop-lit/ddlm2013.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int i;
  int j;
  int a;
  int b;
  int flag;
  tmp_1 = __VERIFIER_nondet_int();
  flag = tmp_1;
  a = 0;
  b = 0;
  j = 1;
  if (flag != 0) {
    i = 0;
  } else {
    i = 1;
  }
  while (true) {
    tmp_2 = __VERIFIER_nondet_int();
    if (!(tmp_2 != 0)) {
      break;
    }
    a = a + 1;
    b = b + (j - i);
    i = i + 2;
    if (i % 2 == 0) {
      j = j + 2;
    } else {
      j = j + 1;
    }
  }
  if (flag != 0) {
    assert(a == b);
  }
  result = 0;
  return result;
}

