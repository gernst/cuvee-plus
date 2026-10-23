// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-lit/hhk2008.c
// SV-COMP loop-lit/hhk2008.yml, translated from benchmarks/sv-comp/dafny/loop-lit/hhk2008.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "hhk2008.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int res = __VERIFIER_nondet_int();
  int cnt = __VERIFIER_nondet_int();
  a = __VERIFIER_nondet_int();
  b = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= b);
  res = a;
  cnt = b;
  while (cnt > 0) {
    cnt = cnt - 1;
    res = res + 1;
  }
  __VERIFIER_assert(res == a + b);
}

