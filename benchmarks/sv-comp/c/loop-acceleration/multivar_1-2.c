// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/multivar_1-2.c
// SV-COMP loop-acceleration/multivar_1-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/multivar_1-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  int y;
  __VERIFIER_assume(0 < N);
  x = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= x);
  y = x + 1;
  while (x < N) {
    x = x + 1;
    y = y + 1;
  }
  assert(x == y);
}

