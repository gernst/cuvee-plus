// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-lit/mcmillan2006.c
// SV-COMP loop-lit/mcmillan2006.yml, translated from benchmarks/sv-comp/dafny/loop-lit/mcmillan2006.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "mcmillan2006.c", 7, "reach_error"); }
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
  int n = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= n);
  i = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && n <= N && N <= 536870911);
  int x[N];
  while (i < n) {
    x[i] = 0;
    i = i + 1;
  }
  i = 0;
  while (i < n) {
    __VERIFIER_assert(x[i] == 0);
    i = i + 1;
  }
}

