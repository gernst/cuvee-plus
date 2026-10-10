// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/mbpr3.c
// SV-COMP array-tiling/mbpr3.yml, translated from benchmarks/sv-comp/dafny/array-tiling/mbpr3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int CELLCOUNT;

int main(void) {
  int result;
  int MINVAL;
  int i;
  int volArray[];
  int CCCELVOL3;
  int CCCELVOL2;
  int CCCELVOL1;
  CELLCOUNT = __VERIFIER_nondet_int();
  if (CELLCOUNT > 1) {
    MINVAL = 2;
    CCCELVOL3 = 7;
    CCCELVOL2 = 3;
    CCCELVOL1 = 1;
    if (CELLCOUNT % 3 != 0) {
      result = 1;
      return result;
    }
    __VERIFIER_assume(CELLCOUNT % 3 == 0);
    i = 1;
    while (i <= CELLCOUNT / 3) {
      if (CCCELVOL3 >= MINVAL) {
        volArray[i * 3 - 3] = CCCELVOL3;
      } else {
        volArray[i * 3 - 3] = 0;
      }
      volArray[i * 3 - 2] = volArray[i * 3 - 2];
      volArray[i * 3 - 1] = volArray[i * 3 - 1];
      i = i + 1;
    }
    i = 1;
    while (i <= CELLCOUNT / 3) {
      if (CCCELVOL2 >= MINVAL) {
        volArray[i * 3 - 2] = CCCELVOL2;
      } else {
        volArray[i * 3 - 2] = 0;
      }
      volArray[i * 3 - 3] = volArray[i * 3 - 3];
      volArray[i * 3 - 1] = volArray[i * 3 - 1];
      i = i + 1;
    }
    i = 1;
    while (i <= CELLCOUNT / 3) {
      if (CCCELVOL1 >= MINVAL) {
        volArray[i * 3 - 1] = CCCELVOL1;
      } else {
        volArray[i * 3 - 1] = 0;
      }
      volArray[i * 3 - 2] = volArray[i * 3 - 2];
      volArray[i * 3 - 3] = volArray[i * 3 - 3];
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

