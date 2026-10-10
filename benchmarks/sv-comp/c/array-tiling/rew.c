// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/rew.c
// SV-COMP array-tiling/rew.yml, translated from benchmarks/sv-comp/dafny/array-tiling/rew.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int S;
  int i;
  int a[];
  S = __VERIFIER_nondet_int();
  if (S > 1) {
    i = 0;
    while (i < S) {
      if (i + 1 < S) {
        a[i + 1] = 0;
      }
      a[i] = 3;
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      assert(a[i] >= 2);
      i = i + 1;
    }
  }
}

