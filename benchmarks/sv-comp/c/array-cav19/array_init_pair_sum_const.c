// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_init_pair_sum_const.c
// SV-COMP array-cav19/array_init_pair_sum_const.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_init_pair_sum_const.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_init_pair_sum_const.c", 7, "reach_error"); }
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
  assume_abort_if_not(0 <= N && N <= 134217727);
  int a[N];
  int b[N];
  int c[N];
  assume_abort_if_not(0 < N);
  i = 0;
  while (i < N) {
    a[i] = 1;
    b[i] = 2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    c[i] = a[i] + b[i];
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    __VERIFIER_assert(c[i] >= 3);
    i = i + 1;
  }
}

