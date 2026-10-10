// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/pnr3.c
// SV-COMP array-tiling/pnr3.yml, translated from benchmarks/sv-comp/dafny/array-tiling/pnr3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
    if (SIZE % 3 != 0) {
      result = 1;
      return result;
    }
    __VERIFIER_assume(SIZE % 3 == 0);
    i = 1;
    while (i <= SIZE / 3) {
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 3 - 3] = value;
      } else {
        a[i * 3 - 3] = FIXEDVAL;
      }
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 3 - 2] = value;
      } else {
        a[i * 3 - 2] = FIXEDVAL;
      }
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 3 - 1] = value;
      } else {
        a[i * 3 - 1] = FIXEDVAL;
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

