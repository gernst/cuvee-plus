// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/hhk2008.c
// SV-COMP loop-lit/hhk2008.yml, translated from benchmarks/sv-comp/dafny/loop-lit/hhk2008.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int a;
  int b;
  int res;
  int cnt;
  a = __VERIFIER_nondet_int();
  b = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= b);
  res = a;
  cnt = b;
  while (cnt > 0) {
    cnt = cnt - 1;
    res = res + 1;
  }
  assert(res == a + b);
}

