// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/rewnifrev.c
// SV-COMP array-tiling/rewnifrev.yml, translated from benchmarks/sv-comp/dafny/array-tiling/rewnifrev.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int SIZE;

int main(void) {
  int result;
  int i;
  int a[];
  SIZE = __VERIFIER_nondet_int();
  if (SIZE > 1) {
    i = SIZE - 1;
    while (i >= 0) {
      if (i - 1 >= 0) {
        a[i - 1] = i - 2;
      }
      a[i] = i;
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

