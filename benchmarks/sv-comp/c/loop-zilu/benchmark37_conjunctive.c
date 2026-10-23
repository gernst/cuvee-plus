// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-zilu/benchmark37_conjunctive.c
// SV-COMP loop-zilu/benchmark37_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark37_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark37_conjunctive.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
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
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  y = tmp_2;
  if (!(x == y && x >= 0)) {
    result = 0;
    return result;
  }
  while (x > 0) {
    x = x - 1;
    y = y - 1;
  }
  __VERIFIER_assert(y >= 0);
  result = 0;
  return result;
}

