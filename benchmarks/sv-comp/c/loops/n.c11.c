// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/n.c11.c
// SV-COMP loops/n.c11.yml, translated from benchmarks/sv-comp/dafny/loops/n.c11.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  _Bool tmp_1;
  int a[];
  int len;
  int i;
  len = 0;
  while (true) {
    tmp_1 = __VERIFIER_nondet_bool();
    if (!tmp_1) {
      break;
    }
    if (len == 4) {
      len = 0;
    }
    a[len] = 0;
    len = len + 1;
  }
  assert(len >= 0 && len < 5);
  result = 1;
  return result;
}

