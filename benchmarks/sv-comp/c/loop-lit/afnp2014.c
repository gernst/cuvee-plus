// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/afnp2014.c
// SV-COMP loop-lit/afnp2014.yml, translated from benchmarks/sv-comp/dafny/loop-lit/afnp2014.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  int y;
  int c;
  __VERIFIER_assume(0 < N);
  x = 1;
  y = 0;
  c = __VERIFIER_nondet_int();
  while (y < N && c != 0) {
    x = x + y;
    y = y + 1;
    c = __VERIFIER_nondet_int();
  }
  assert(x >= y);
}

