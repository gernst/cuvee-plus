// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-fpi/ncomp.c
// SV-COMP array-fpi/ncomp.yml, translated from benchmarks/sv-comp/dafny/array-fpi/ncomp.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "ncomp.c", 7, "reach_error"); }
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
  N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 134217727);
  assume_abort_if_not(0 < N);
  int a[N], b[N], c[N];
  a[0] = 6;
  b[0] = 1;
  c[0] = N;
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
  i = 1;
  while (i < N) {
    c[i] = c[i - 1] + b[i - 1];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    __VERIFIER_assert(c[i] == N + i * i * i);
    i = i + 1;
  }
}

