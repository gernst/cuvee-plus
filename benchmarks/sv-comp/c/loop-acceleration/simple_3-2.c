// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/simple_3-2.c
// SV-COMP loop-acceleration/simple_3-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_3-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int x;
  int N;
  x = 0;
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= N);
  while (x < N) {
    x = x + 2;
  }
  assert(x % 2 == 0);
}

