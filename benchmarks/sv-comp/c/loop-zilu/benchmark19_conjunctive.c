// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-zilu/benchmark19_conjunctive.c
// SV-COMP loop-zilu/benchmark19_conjunctive.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark19_conjunctive.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark19_conjunctive.c", 7, "reach_error"); }
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
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  j = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  k = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  n = tmp_3;
  if (!(j == n && k == n && n > 0)) {
    result = 0;
    return result;
  }
  while (j > 0 && n > 0) {
    j = j - 1;
    k = k - 1;
  }
  __VERIFIER_assert(k == 0);
  result = 0;
  return result;
}

