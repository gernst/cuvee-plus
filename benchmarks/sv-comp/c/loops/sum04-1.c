// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/sum04-1.c
// SV-COMP loops/sum04-1.yml, translated from benchmarks/sv-comp/dafny/loops/sum04-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sum04-1.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int sn = __VERIFIER_nondet_int();
  sn = 0;
  i = 1;
  while (i <= 8) {
    if (i < 4) {
      sn = sn + 2;
    }
    i = i + 1;
  }
  __VERIFIER_assert(sn == 8 * 2 || sn == 0);
}

