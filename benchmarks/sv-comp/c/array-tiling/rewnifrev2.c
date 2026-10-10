// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/rewnifrev2.c
// SV-COMP array-tiling/rewnifrev2.yml, translated from benchmarks/sv-comp/dafny/array-tiling/rewnifrev2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int SIZE;

int main(void) {
  int result;
  int i;
  int a[];
  SIZE = __VERIFIER_nondet_int();
  if (SIZE > 1) {
    i = SIZE - 2;
    while (i >= 0) {
      a[i] = i;
      a[i + 1] = i + 1;
      i = i - 1;
    }
    i = 0;
    while (i < SIZE) {
      assert(a[i] >= i);
      i = i + 1;
    }
  }
  result = 1;
  return result;
}

