// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-acceleration/phases_1-1.c
// SV-COMP loop-acceleration/phases_1-1.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/phases_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int x;
  __VERIFIER_assume(65520 < N);
  x = 0;
  while (x < N) {
    if (x < 65520) {
      x = x + 1;
    } else {
      x = x + 2;
    }
  }
  assert(x % 2 == 0);
}

