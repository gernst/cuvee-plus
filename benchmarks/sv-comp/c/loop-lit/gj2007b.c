// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/gj2007b.c
// SV-COMP loop-lit/gj2007b.yml, translated from benchmarks/sv-comp/dafny/loop-lit/gj2007b.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int m;
  int n;
  int b;
  x = 0;
  m = 0;
  n = __VERIFIER_nondet_int();
  while (x < n) {
    b = __VERIFIER_nondet_int();
    if (b != 0) {
      m = x;
    }
    x = x + 1;
  }
  assert(m >= 0 || n <= 0);
  assert(m < n || n <= 0);
}

