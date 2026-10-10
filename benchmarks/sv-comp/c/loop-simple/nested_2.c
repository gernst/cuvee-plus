// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-simple/nested_2.c
// SV-COMP loop-simple/nested_2.yml, translated from benchmarks/sv-comp/dafny/loop-simple/nested_2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int a;
  int b;
  __VERIFIER_assume(0 < N);
  a = N;
  b = N;
  a = 0;
  while (a < N) {
    b = 0;
    while (b < N) {
      b = b + 1;
    }
    a = a + 1;
  }
  assert(a == N && b == N);
}

