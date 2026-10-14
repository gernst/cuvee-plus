// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/s3if.c
// SV-COMP array-fpi/s3if.yml, translated from benchmarks/sv-comp/dafny/array-fpi/s3if.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "s3if.c", 7, "reach_error"); }
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
  int sum = __VERIFIER_nondet_int();
  N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  assume_abort_if_not(0 < N);
  int a[N];
  sum = 0;
  i = 0;
  while (i < N) {
    a[i] = 3;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] == 3) {
      sum = sum + a[i];
    } else {
      sum = sum * a[i];
    }
    i = i + 1;
  }
  __VERIFIER_assert(sum == 3 * N);
}

