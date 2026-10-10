// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/mcmillan2006.c
// SV-COMP loop-lit/mcmillan2006.yml, translated from benchmarks/sv-comp/dafny/loop-lit/mcmillan2006.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int n;
  int x[];
  int i;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
  i = 0;
  while (i < n) {
    x[i] = 0;
    i = i + 1;
  }
  i = 0;
  while (i < n) {
    assert(x[i] == 0);
    i = i + 1;
  }
}

