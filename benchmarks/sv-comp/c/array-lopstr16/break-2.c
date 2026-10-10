// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/break-2.c
// SV-COMP array-lopstr16/break-2.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/break-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int s[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    if (i > N / 2) {
      break;
    }
    s[i] = 10;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i <= N / 2) {
      assert(s[i] == 10);
    }
    i = i + 1;
  }
}

