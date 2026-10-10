// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/nr5.c
// SV-COMP array-tiling/nr5.yml, translated from benchmarks/sv-comp/dafny/array-tiling/nr5.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int CELLCOUNT;

int main(void) {
  int result;
  int DEFAULTVALUE;
  int MINVAL;
  int i;
  int j;
  int volArray[];
  CELLCOUNT = __VERIFIER_nondet_int();
  if (CELLCOUNT > 1) {
    DEFAULTVALUE = 1;
    MINVAL = 2;
    if (CELLCOUNT % 5 != 0) {
      result = 1;
      return result;
    }
    __VERIFIER_assume(CELLCOUNT % 5 == 0);
    i = 1;
    while (i <= CELLCOUNT / 5) {
      j = 5;
      while (j >= 1) {
        if (j >= MINVAL) {
          volArray[i * 5 - j] = j;
        } else {
          volArray[i * 5 - j] = 0;
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

