// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_init_nondet_vars.c
// SV-COMP array-cav19/array_init_nondet_vars.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_init_nondet_vars.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_init_nondet_vars.c", 7, "reach_error"); }
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
  int j = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(j > 0 && j <= 536870911);
  i = 1;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && n <= N && N <= 536870911);
  int a[N];
  while (i < n) {
    k = __VERIFIER_nondet_int();
    assume_abort_if_not(k > 0 && k <= 536870911);
    a[i] = i + j + k;
    i = i + 1;
  }
  i = 1;
  while (i < n) {
    __VERIFIER_assert(a[i] >= i + 2);
    i = i + 1;
  }
}

