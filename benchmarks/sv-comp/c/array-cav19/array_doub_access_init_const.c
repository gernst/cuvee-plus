// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_doub_access_init_const.c
// SV-COMP array-cav19/array_doub_access_init_const.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_doub_access_init_const.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_doub_access_init_const.c", 7, "reach_error"); }
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
  int i = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  N = __VERIFIER_nondet_int();
  int M = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= M && N < M && 2 * N + 1 < M && M <= 536870911);
  assume_abort_if_not(0 < N);
  int a[M];
  i = 0;
  while (i <= N) {
    a[2 * i] = 0;
    a[2 * i + 1] = 0;
    i = i + 1;
  }
  i = 0;
  while (i <= 2 * N) {
    __VERIFIER_assert(a[i] >= 0);
    i = i + 1;
  }
}

