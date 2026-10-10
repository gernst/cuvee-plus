// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/nr2.c
// SV-COMP array-tiling/nr2.yml, translated from benchmarks/sv-comp/dafny/array-tiling/nr2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int C;
  int i;
  int j;
  int MINVAL;
  int a[];
  C = __VERIFIER_nondet_int();
  if (C > 1) {
    MINVAL = 2;
    if (C % 2 != 0) {
      return;
    }
    i = 1;
    while (i <= C / 2) {
      j = 2;
      while (j >= 1) {
        if (j >= MINVAL) {
          a[i * 2 - j] = j;
        } else {
          a[i * 2 - j] = 0;
        }
        j = j - 1;
      }
      i = i + 1;
    }
    i = 0;
    while (i < C) {
      assert(a[i] >= MINVAL || a[i] == 0);
      i = i + 1;
    }
  }
}

