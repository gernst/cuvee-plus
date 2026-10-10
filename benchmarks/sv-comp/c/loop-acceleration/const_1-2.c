// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/const_1-2.c
// SV-COMP loop-acceleration/const_1-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/const_1-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int x;
  int y;
  __VERIFIER_assume(0 < N);
  x = 1;
  y = 0;
  while (y < N) {
    x = 0;
    y = y + 1;
  }
  assert(x == 1);
}

