// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/mbpr2.c
// SV-COMP array-tiling/mbpr2.yml, translated from benchmarks/sv-comp/dafny/array-tiling/mbpr2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int C;
  int i;
  int MINVAL;
  int V2;
  int V1;
  int a[];
  C = __VERIFIER_nondet_int();
  if (C > 1) {
    MINVAL = 2;
    V2 = 3;
    V1 = 1;
    if (C % 2 != 0) {
      return;
    }
    i = 1;
    while (i <= C / 2) {
      if (V2 >= MINVAL) {
        a[i * 2 - 2] = V2;
      } else {
        a[i * 2 - 2] = 0;
      }
      a[i * 2 - 1] = a[i * 2 - 1];
      i = i + 1;
    }
    i = 1;
    while (i <= C / 2) {
      if (V1 >= MINVAL) {
        a[i * 2 - 1] = V1;
      } else {
        a[i * 2 - 1] = 0;
      }
      a[i * 2 - 2] = a[i * 2 - 2];
      i = i + 1;
    }
    i = 0;
    while (i < C) {
      assert(a[i] >= MINVAL || a[i] == 0);
      i = i + 1;
    }
  }
}

