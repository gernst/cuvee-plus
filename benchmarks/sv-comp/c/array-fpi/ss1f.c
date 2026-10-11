// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-fpi/ss1f.c
// SV-COMP array-fpi/ss1f.yml, translated from benchmarks/sv-comp/dafny/array-fpi/ss1f.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "ss1f.c", 7, "reach_error"); }
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
  int a[N];
  assume_abort_if_not(0 < N);
  sum = 0;
  i = 0;
  while (i < N) {
    a[i] = 2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum = sum + a[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    a[i] = a[i] + sum;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    sum = sum + a[i];
    i = i + 1;
  }
  __VERIFIER_assert(sum == N * (N + 2));
}

