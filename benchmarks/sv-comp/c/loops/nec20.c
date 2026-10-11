// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/nec20.c
// SV-COMP loops/nec20.yml, translated from benchmarks/sv-comp/dafny/loops/nec20.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nec20.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
void assume_abort_if_not(int cond) {
  if (!cond) { abort(); }
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int b;

int main(void) {
  int result = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  _Bool tmp_1 = __VERIFIER_nondet_bool();
  _Bool k = __VERIFIER_nondet_bool();
  int i = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int a[N];
  assume_abort_if_not(1 < N);
  tmp_1 = __VERIFIER_nondet_bool();
  k = tmp_1;
  if (k) {
    n = 0;
  } else {
    n = N - 1;
  }
  i = 0;
  j = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= j);
  while (i <= n) {
    i = i + 1;
    j = j + 2;
  }
  a[i] = 0;
  __VERIFIER_assert(j < N + 1);
  a[j] = 0;
  a[b] = 0;
  if (b >= 0 && b < N - 1) {
    a[b] = 1;
  } else {
    a[b % (N - 1)] = 1;
  }
  result = 1;
  return result;
}

