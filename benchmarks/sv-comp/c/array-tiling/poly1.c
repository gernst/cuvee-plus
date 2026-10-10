// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/poly1.c
// SV-COMP array-tiling/poly1.yml, translated from benchmarks/sv-comp/dafny/array-tiling/poly1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int S;
  int i;
  int a[];
  S = __VERIFIER_nondet_int();
  if (S > 1) {
    i = 0;
    while (i < S) {
      a[i] = i * i;
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      assert(a[i] == i * i);
      i = i + 1;
    }
  }
}

