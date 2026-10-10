// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/skippedu.c
// SV-COMP array-tiling/skippedu.yml, translated from benchmarks/sv-comp/dafny/array-tiling/skippedu.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int S;
  int i;
  int v;
  int a[];
  S = __VERIFIER_nondet_int();
  if (S > 1) {
    i = 0;
    while (i < S) {
      v = __VERIFIER_nondet_int();
      a[i] = v;
      i = i + 1;
    }
    if (S % 2 != 0) {
      return;
    }
    i = 1;
    while (i <= S / 2) {
      if (a[2 * i - 2] > i) {
        a[2 * i - 2] = i;
      }
      if (a[2 * i - 1] > i) {
        a[2 * i - 1] = i;
      }
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      assert(a[i] <= i);
      i = i + 1;
    }
  }
}

