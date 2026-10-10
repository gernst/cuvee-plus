// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/multivar_1-1.c
// SV-COMP loop-acceleration/multivar_1-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/multivar_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  int y;
  __VERIFIER_assume(0 < N);
  x = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= x);
  y = x;
  while (x < N) {
    x = x + 1;
    y = y + 1;
  }
  assert(x == y);
}

