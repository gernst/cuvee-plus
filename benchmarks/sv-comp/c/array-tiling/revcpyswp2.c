// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/revcpyswp2.c
// SV-COMP array-tiling/revcpyswp2.yml, translated from benchmarks/sv-comp/dafny/array-tiling/revcpyswp2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int S;
  int i;
  int tmp;
  int v;
  int a[];
  int b[];
  int ac[];
  int bc[];
  S = __VERIFIER_nondet_int();
  if (S > 1) {
    i = 0;
    while (i < S) {
      v = __VERIFIER_nondet_int();
      ac[i] = v;
      v = __VERIFIER_nondet_int();
      bc[i] = v;
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      a[i] = ac[S - i - 1];
      b[i] = bc[S - i - 1];
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      tmp = a[i];
      a[i] = b[i];
      b[i] = tmp;
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      tmp = a[i];
      a[i] = b[i];
      b[i] = tmp;
      i = i + 1;
    }
    i = 0;
    while (i < S) {
      assert(a[i] == ac[S - i - 1]);
      i = i + 1;
    }
  }
}

