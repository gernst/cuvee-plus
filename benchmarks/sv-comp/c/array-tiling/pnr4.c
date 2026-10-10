// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/pnr4.c
// SV-COMP array-tiling/pnr4.yml, translated from benchmarks/sv-comp/dafny/array-tiling/pnr4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ReadFromPort(void) {
  int result;
  int tmp_1;
  int x;
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  result = x;
  return result;
}

int SIZE;

int main(void) {
  int result;
  int i;
  int value;
  int a[];
  int DEFAULTVAL;
  int FIXEDVAL;
  SIZE = __VERIFIER_nondet_int();
  if (SIZE > 1) {
    DEFAULTVAL = 0;
    FIXEDVAL = 10;
    if (SIZE % 4 != 0) {
      result = 1;
      return result;
    }
    __VERIFIER_assume(SIZE % 4 == 0);
    i = 1;
    while (i <= SIZE / 4) {
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 4 - 4] = value;
      } else {
        a[i * 4 - 4] = FIXEDVAL;
      }
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 4 - 3] = value;
      } else {
        a[i * 4 - 3] = FIXEDVAL;
      }
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 4 - 2] = value;
      } else {
        a[i * 4 - 2] = FIXEDVAL;
      }
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 4 - 1] = value;
      } else {
        a[i * 4 - 1] = FIXEDVAL;
      }
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      assert(a[i] != DEFAULTVAL);
      i = i + 1;
    }
  }
  result = 1;
  return result;
}

