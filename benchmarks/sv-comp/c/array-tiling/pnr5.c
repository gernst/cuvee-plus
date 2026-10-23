// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-tiling/pnr5.c
// SV-COMP array-tiling/pnr5.yml, translated from benchmarks/sv-comp/dafny/array-tiling/pnr5.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "pnr5.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void assume_abort_if_not(int cond) {
  if (!cond) { abort(); }
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int ReadFromPort(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  result = x;
  return result;
}

int SIZE;

int main(void) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int value = __VERIFIER_nondet_int();
  int DEFAULTVAL = __VERIFIER_nondet_int();
  int FIXEDVAL = __VERIFIER_nondet_int();
  SIZE = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && SIZE / 5 < N && SIZE <= N && N <= 536870911);
  int a[N];
  if (SIZE > 1) {
    DEFAULTVAL = 0;
    FIXEDVAL = 10;
    if (SIZE % 5 != 0) {
      result = 1;
      return result;
    }
    assume_abort_if_not(SIZE % 5 == 0);
    i = 1;
    while (i <= SIZE / 5) {
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 5 - 5] = value;
      } else {
        a[i * 5 - 5] = FIXEDVAL;
      }
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 5 - 4] = value;
      } else {
        a[i * 5 - 4] = FIXEDVAL;
      }
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 5 - 3] = value;
      } else {
        a[i * 5 - 3] = FIXEDVAL;
      }
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 5 - 2] = value;
      } else {
        a[i * 5 - 2] = FIXEDVAL;
      }
      value = ReadFromPort();
      if (value != DEFAULTVAL) {
        a[i * 5 - 1] = value;
      } else {
        a[i * 5 - 1] = FIXEDVAL;
      }
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      __VERIFIER_assert(a[i] != DEFAULTVAL);
      i = i + 1;
    }
  }
  result = 1;
  return result;
}

