// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-lopstr16/scalar_loopdep.c
// SV-COMP array-lopstr16/scalar_loopdep.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/scalar_loopdep.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "scalar_loopdep.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  assume_abort_if_not(0 < N);
  int a[N];
  y = 100;
  i = 0;
  while (i < N) {
    x = y;
    a[i] = y;
    y = y + 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    __VERIFIER_assert(a[i] >= 100);
    i = i + 1;
  }
}

