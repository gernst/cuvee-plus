// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/cggmp2005b.c
// SV-COMP loop-lit/cggmp2005b.yml, translated from benchmarks/sv-comp/dafny/loop-lit/cggmp2005b.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int M;
  int i;
  int j;
  int k;
  __VERIFIER_assume(0 < N);
  __VERIFIER_assume(0 < M);
  i = 0;
  k = 9;
  j = -N;
  while (i <= N) {
    i = i + 1;
    while (j < M) {
      j = i + j;
    }
    k = 4;
    while (k <= 3) {
      k = k + 1;
    }
  }
  assert(k == 4);
  result = 0;
  return result;
}

