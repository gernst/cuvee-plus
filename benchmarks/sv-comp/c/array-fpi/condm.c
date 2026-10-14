// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-fpi/condm.c
// SV-COMP array-fpi/condm.yml, translated from benchmarks/sv-comp/dafny/array-fpi/condm.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "condm.c", 7, "reach_error"); }
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
  assume_abort_if_not(0 <= N && N <= 536870911);
  assume_abort_if_not(0 < N);
  int a[N];
  i = 0;
  while (i < N) {
    a[i] = 0;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (N % 2 == 0) {
      a[i] = a[i] + 2;
    } else {
      a[i] = a[i] + 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    __VERIFIER_assert(a[i] % 2 == N % 2);
    i = i + 1;
  }
}

