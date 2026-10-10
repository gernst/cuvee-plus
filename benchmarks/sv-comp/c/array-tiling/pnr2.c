// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/pnr2.c
// SV-COMP array-tiling/pnr2.yml, translated from benchmarks/sv-comp/dafny/array-tiling/pnr2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int S;
  int i;
  int value;
  int a[];
  S = __VERIFIER_nondet_int();
  if (S > 1) {
    if (S % 2 != 0) {
      return;
    }
    i = 1;
    while (i <= S / 2) {
      value = __VERIFIER_nondet_int();
      if (value != 0) {
        a[i * 2 - 2] = value;
      } else {
        a[i * 2 - 2] = 10;
      }
      value = __VERIFIER_nondet_int();
      if (value != 0) {
        a[i * 2 - 1] = value;
      } else {
        a[i * 2 - 1] = 10;
      }
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      assert(a[i] != 0);
      i = i + 1;
    }
  }
}

