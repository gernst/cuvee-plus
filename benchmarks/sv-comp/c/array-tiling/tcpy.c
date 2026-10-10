// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/tcpy.c
// SV-COMP array-tiling/tcpy.yml, translated from benchmarks/sv-comp/dafny/array-tiling/tcpy.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int SIZE;

int main(void) {
  int result;
  int tmp_1;
  int i;
  int a[];
  int acopy[];
  SIZE = __VERIFIER_nondet_int();
  if (SIZE > 1) {
    i = 0;
    while (i < SIZE) {
      tmp_1 = __VERIFIER_nondet_int();
      a[i] = tmp_1;
      i = i + 1;
    }
    if (SIZE % 2 != 0) {
      result = 1;
      return result;
    }
    __VERIFIER_assume(SIZE % 2 == 0);
    i = 0;
    while (i < SIZE / 2) {
      acopy[SIZE - i - 1] = a[SIZE - i - 1];
      acopy[i] = a[i];
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      assert(acopy[i] == a[i]);
      i = i + 1;
    }
  }
  result = 1;
  return result;
}

