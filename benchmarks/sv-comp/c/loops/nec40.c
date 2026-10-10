// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/nec40.c
// SV-COMP loops/nec40.yml, translated from benchmarks/sv-comp/dafny/loops/nec40.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int x[];
  int y[];
  int i;
  int j;
  int k;
  x[0] = 0;
  k = __VERIFIER_nondet_int();
  i = 0;
  while (x[i] != 0) {
    y[i] = x[i];
    i = i + 1;
  }
  y[i] = 0;
  if (k >= 0 && k < i) {
    if (y[k] != 0) {
      assert(0 != 0);
    }
  }
  result = 0;
  return result;
}

