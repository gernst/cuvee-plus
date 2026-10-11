// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/s2liff.c
// SV-COMP array-fpi/s2liff.yml, translated from benchmarks/sv-comp/dafny/array-fpi/s2liff.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "s2liff.c", 7, "reach_error"); }
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
  sum[0] = N;
  i = 0;
  while (i < N) {
    a[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (a[i] == 1) {
      a[i] = a[i] + 2;
    } else {
      a[i] = a[i] - 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum[0] = sum[0] + a[i];
    i = i + 1;
  }
  __VERIFIER_assert(sum[0] == 3 * N);
  result = 1;
  return result;
}

