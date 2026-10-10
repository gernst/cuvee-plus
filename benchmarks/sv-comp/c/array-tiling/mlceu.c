// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/mlceu.c
// SV-COMP array-tiling/mlceu.yml, translated from benchmarks/sv-comp/dafny/array-tiling/mlceu.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int S;
  int i;
  int a[];
  S = __VERIFIER_nondet_int();
  if (S <= 0) {
    return;
  }
  i = 0;
  while (i < S) {
    if (i / 65536 > 250) {
      a[i] = 1;
    } else {
      a[i] = 0;
    }
    i = i + 1;
  }
  i = 0;
  while (i < S) {
    assert(a[i] == 0);
    i = i + 1;
  }
}

