// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/bhmr2007.c
// SV-COMP loop-lit/bhmr2007.yml, translated from benchmarks/sv-comp/dafny/loop-lit/bhmr2007.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int n;
  int a;
  int b;
  i = 0;
  a = 0;
  b = 0;
  n = __VERIFIER_nondet_int();
  if (!(n >= 0)) {
    result = 0;
    return result;
  }
  while (i < n) {
    tmp_1 = __VERIFIER_nondet_int();
    if (tmp_1 != 0) {
      a = a + 1;
      b = b + 2;
    } else {
      a = a + 2;
      b = b + 1;
    }
    i = i + 1;
  }
  assert(a + b == 3 * n);
  result = 0;
  return result;
}

