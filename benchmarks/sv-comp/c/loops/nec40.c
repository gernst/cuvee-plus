// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/nec40.c
// SV-COMP loops/nec40.yml, translated from benchmarks/sv-comp/dafny/loops/nec40.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nec40.c", 7, "reach_error"); }
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

int main(void) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && 0 < N && N <= 268435455);
  int x[N];
  int y[N];
  x[0] = 0;
  k = __VERIFIER_nondet_int();
  i = 0;
  while (x[i] != 0) {
    y[i] = x[i];
    i = i + 1;
  }
  y[i] = 0;
  if (k >= 0 && k < i) {
    if (y[k] != 0) {
      __VERIFIER_assert(0 != 0);
    }
  }
  result = 0;
  return result;
}

