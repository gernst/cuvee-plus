// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/nr4.c
// SV-COMP array-tiling/nr4.yml, translated from benchmarks/sv-comp/dafny/array-tiling/nr4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int CELLCOUNT;

int main(void) {
  int result;
  int MINVAL;
  int i;
  int j;
  int volArray[];
  CELLCOUNT = __VERIFIER_nondet_int();
  if (CELLCOUNT > 1) {
    MINVAL = 2;
    if (CELLCOUNT % 4 != 0) {
      result = 1;
      return result;
    }
    __VERIFIER_assume(CELLCOUNT % 4 == 0);
    i = 1;
    while (i <= CELLCOUNT / 4) {
      j = 4;
      while (j >= 1) {
        if (j >= MINVAL) {
          volArray[i * 4 - j] = j;
        } else {
          volArray[i * 4 - j] = 0;
        }
        j = j - 1;
      }
      i = i + 1;
    }
    i = 0;
    while (i < CELLCOUNT) {
      assert(volArray[i] >= MINVAL || volArray[i] == 0);
      i = i + 1;
    }
  }
  result = 1;
  return result;
}

