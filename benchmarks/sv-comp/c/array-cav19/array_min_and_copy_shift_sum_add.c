// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_min_and_copy_shift_sum_add.c
// SV-COMP array-cav19/array_min_and_copy_shift_sum_add.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_min_and_copy_shift_sum_add.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_min_and_copy_shift_sum_add.c", 7, "reach_error"); }
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

void main(void) {
  int N = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  k = 0;
  N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  int a[N], b[N];
  i = 0;
  while (i < N) {
    if (j > a[i]) {
      j = a[i];
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b[i] = a[i] - j;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    k = k + b[i] + i;
    i = i + 1;
  }
  __VERIFIER_assert(k >= 0);
}

