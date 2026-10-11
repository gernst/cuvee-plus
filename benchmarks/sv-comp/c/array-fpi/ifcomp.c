// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-fpi/ifcomp.c
// SV-COMP array-fpi/ifcomp.yml, translated from benchmarks/sv-comp/dafny/array-fpi/ifcomp.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "ifcomp.c", 7, "reach_error"); }
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
  int a[N];
  int b[N];
  int c[N];
  assume_abort_if_not(0 < N);
  i = 0;
  while (i < N) {
    if (i == 0) {
      a[0] = 6;
    } else {
      a[i] = a[i - 1] + 6;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i == 0) {
      b[0] = 1;
    } else {
      b[i] = b[i - 1] + a[i - 1];
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (i == 0) {
      c[0] = 0;
    } else {
      c[i] = c[i - 1] + b[i - 1];
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    __VERIFIER_assert(c[i] == i * i * i);
    i = i + 1;
  }
}

