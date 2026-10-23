// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops/sum01-2.c
// SV-COMP loops/sum01-2.yml, translated from benchmarks/sv-comp/dafny/loops/sum01-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sum01-2.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int i = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int sn = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  sn = 0;
  i = 1;
  while (i <= n) {
    sn = sn + 2;
    i = i + 1;
  }
  __VERIFIER_assert(sn == n * 2 || sn == 0);
}

