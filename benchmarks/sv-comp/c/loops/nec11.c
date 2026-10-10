// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/nec11.c
// SV-COMP loops/nec11.yml, translated from benchmarks/sv-comp/dafny/loops/nec11.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  _Bool tmp_1;
  int a[];
  int len;
  _Bool c;
  int i;
  len = 0;
  tmp_1 = __VERIFIER_nondet_bool();
  c = tmp_1;
  while (c) {
    if (len == 4) {
      len = 0;
    }
    a[len] = 0;
    len = len + 1;
  }
  assert(len == 5);
  result = 1;
  return result;
}

