// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/sum03-2.c
// SV-COMP loops/sum03-2.yml, translated from benchmarks/sv-comp/dafny/loops/sum03-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sum03-2.c", 7, "reach_error"); }
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
  int tmp_2 = __VERIFIER_nondet_int();
  int sn = __VERIFIER_nondet_int();
  int loop1 = __VERIFIER_nondet_int();
  int n1 = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  sn = 0;
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  loop1 = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_2);
  n1 = tmp_2;
  x = 0;
  while (1 != 0) {
    sn = sn + 2;
    x = x + 1;
    __VERIFIER_assert(sn == x * 2 || sn == 0);
  }
}

