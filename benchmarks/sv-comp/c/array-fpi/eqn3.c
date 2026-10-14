// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/eqn3.c
// SV-COMP array-fpi/eqn3.yml, translated from benchmarks/sv-comp/dafny/array-fpi/eqn3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "eqn3.c", 7, "reach_error"); }
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
  int a[N], b[N];
  if (N <= 0) {
    result = 1;
    return result;
  }
  a[0] = 6;
  b[0] = 1;
  i = 1;
  while (i < N) {
    a[i] = a[i - 1] + 6;
    i = i + 1;
  }
  i = 1;
  while (i < N) {
    b[i] = b[i - 1] + a[i - 1];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    __VERIFIER_assert(b[i] == 3 * i * i + 3 * i + 1);
    i = i + 1;
  }
  result = 1;
  return result;
}

