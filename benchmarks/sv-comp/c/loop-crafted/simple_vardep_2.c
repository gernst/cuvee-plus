// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-crafted/simple_vardep_2.c
// SV-COMP loop-crafted/simple_vardep_2.yml, translated from benchmarks/sv-comp/dafny/loop-crafted/simple_vardep_2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int j;
  int k;
  __VERIFIER_assume(0 < N);
  i = 0;
  j = 0;
  k = 0;
  while (k < N) {
    i = i + 1;
    j = j + 2;
    k = k + 3;
    assert(k == 3 * i && j == 2 * i);
  }
}

