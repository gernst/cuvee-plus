// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark20_conjunctive.c
// SV-COMP loop-zilu/benchmark20_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark20_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark20_conjunctive.c", 7, "reach_error"); }
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
  int tmp_3 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int sum = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  i = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  n = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  sum = tmp_3;
  if (!(i == 0 && n >= 0 && sum == 0)) {
    result = 0;
    return result;
  }
  while (i < n) {
    sum = sum + i;
    i = i + 1;
  }
  __VERIFIER_assert(sum >= 0);
  result = 0;
  return result;
}

