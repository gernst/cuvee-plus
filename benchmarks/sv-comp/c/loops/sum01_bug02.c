// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/sum01_bug02.c
// SV-COMP loops/sum01_bug02.yml, translated from benchmarks/sv-comp/dafny/loops/sum01_bug02.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sum01_bug02.c", 7, "reach_error"); }
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

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int sn = __VERIFIER_nondet_int();
  j = 10;
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  n = tmp_1;
  sn = 0;
  if (n == 2147483647) {
    result = 0;
    return result;
  }
  i = 1;
  while (i <= n) {
    if (i < j) {
      sn = sn + 2;
    }
    j = j - 1;
    i = i + 1;
  }
  __VERIFIER_assert(sn == n * 2 || sn == 0);
}

