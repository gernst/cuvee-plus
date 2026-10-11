// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/brs2f.c
// SV-COMP array-fpi/brs2f.yml, translated from benchmarks/sv-comp/dafny/array-fpi/brs2f.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "brs2f.c", 7, "reach_error"); }
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

int N;

int main(void) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  int sum[N];
  int a[N];
  if (N <= 0) {
    result = 1;
    return result;
  }
  i = 0;
  while (i < N) {
    if (i % 2 == 0) {
      a[i] = 20;
    } else {
      a[i] = 0;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i == 0) {
      sum[0] = 0;
    } else {
      sum[0] = sum[0] + a[i];
    }
    i = i + 1;
  }
  __VERIFIER_assert(sum[0] <= 2 * N);
  result = 1;
  return result;
}

