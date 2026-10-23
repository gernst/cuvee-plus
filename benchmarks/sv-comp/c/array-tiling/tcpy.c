// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-tiling/tcpy.c
// SV-COMP array-tiling/tcpy.yml, translated from benchmarks/sv-comp/dafny/array-tiling/tcpy.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "tcpy.c", 7, "reach_error"); }
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

int SIZE;

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  SIZE = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && SIZE <= N && SIZE / 2 <= N && N <= 268435455);
  int a[N], acopy[N];
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
    assume_abort_if_not(SIZE % 2 == 0);
    i = 0;
    while (i < SIZE / 2) {
      acopy[SIZE - i - 1] = a[SIZE - i - 1];
      acopy[i] = a[i];
      i = i + 1;
    }
    i = 0;
    while (i < SIZE) {
      __VERIFIER_assert(acopy[i] == a[i]);
      i = i + 1;
    }
  }
  result = 1;
  return result;
}

