// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/rewrev.c
// SV-COMP array-tiling/rewrev.yml, translated from benchmarks/sv-comp/dafny/array-tiling/rewrev.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int S;
  int i;
  int a[];
  S = __VERIFIER_nondet_int();
  if (S > 1) {
    i = S - 2;
    while (i >= -1) {
      if (i >= 0) {
        a[i] = 7;
      }
      a[i + 1] = 3;
      i = i - 1;
    }
    i = 0;
    while (i < S) {
      assert(a[i] >= 2);
      i = i + 1;
    }
  }
}

