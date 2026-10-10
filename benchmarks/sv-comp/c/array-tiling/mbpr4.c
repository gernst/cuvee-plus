// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/mbpr4.c
// SV-COMP array-tiling/mbpr4.yml, translated from benchmarks/sv-comp/dafny/array-tiling/mbpr4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int CELLCOUNT;

int main(void) {
  int result;
  int MINVAL;
  int i;
  int volArray[];
  int CCCELVOL4;
  int CCCELVOL3;
  int CCCELVOL2;
  int CCCELVOL1;
  CELLCOUNT = __VERIFIER_nondet_int();
  if (CELLCOUNT > 1) {
    MINVAL = 2;
    CCCELVOL4 = 5;
    CCCELVOL3 = 7;
    CCCELVOL2 = 3;
    CCCELVOL1 = 1;
    if (CELLCOUNT % 4 != 0) {
      result = 1;
      return result;
    }
    __VERIFIER_assume(CELLCOUNT % 4 == 0);
    i = 1;
    while (i <= CELLCOUNT / 4) {
      if (CCCELVOL4 >= MINVAL) {
        volArray[i * 4 - 4] = CCCELVOL4;
      } else {
        volArray[i * 4 - 4] = 0;
      }
      volArray[i * 4 - 3] = volArray[i * 4 - 3];
      volArray[i * 4 - 2] = volArray[i * 4 - 2];
      volArray[i * 4 - 1] = volArray[i * 4 - 1];
      i = i + 1;
    }
    i = 1;
    while (i <= CELLCOUNT / 4) {
      if (CCCELVOL3 >= MINVAL) {
        volArray[i * 4 - 3] = CCCELVOL3;
      } else {
        volArray[i * 4 - 3] = 0;
      }
      volArray[i * 4 - 4] = volArray[i * 4 - 4];
      volArray[i * 4 - 2] = volArray[i * 4 - 2];
      volArray[i * 4 - 1] = volArray[i * 4 - 1];
      i = i + 1;
    }
    i = 1;
    while (i <= CELLCOUNT / 4) {
      if (CCCELVOL2 >= MINVAL) {
        volArray[i * 4 - 2] = CCCELVOL2;
      } else {
        volArray[i * 4 - 2] = 0;
      }
      volArray[i * 4 - 4] = volArray[i * 4 - 4];
      volArray[i * 4 - 3] = volArray[i * 4 - 3];
      volArray[i * 4 - 1] = volArray[i * 4 - 1];
      i = i + 1;
    }
    i = 1;
    while (i <= CELLCOUNT / 4) {
      if (CCCELVOL1 >= MINVAL) {
        volArray[i * 4 - 1] = CCCELVOL1;
      } else {
        volArray[i * 4 - 1] = 0;
      }
      volArray[i * 4 - 4] = volArray[i * 4 - 4];
      volArray[i * 4 - 3] = volArray[i * 4 - 3];
      volArray[i * 4 - 2] = volArray[i * 4 - 2];
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

