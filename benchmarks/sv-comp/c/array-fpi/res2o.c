// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/res2o.c
// SV-COMP array-fpi/res2o.yml, translated from benchmarks/sv-comp/dafny/array-fpi/res2o.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "res2o.c", 7, "reach_error"); }
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
  assume_abort_if_not(0 <= N && N <= 134217727);
  int sum[N];
  int a[N];
  int b[N];
  int c[N];
  if (N <= 0) {
    result = 1;
    return result;
  }
  sum[0] = 0;
  i = 0;
  while (i < N) {
    a[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    b[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    c[i] = 1;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum[0] = sum[0] + a[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum[0] = sum[0] + b[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum[0] = sum[0] + c[i];
    i = i + 1;
  }
  __VERIFIER_assert(sum[0] <= 3 * N);
  result = 1;
  return result;
}

