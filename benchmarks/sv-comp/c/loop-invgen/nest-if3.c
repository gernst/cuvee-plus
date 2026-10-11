// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/nest-if3.c
// SV-COMP loop-invgen/nest-if3.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/nest-if3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nest-if3.c", 7, "reach_error"); }
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
  int k = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int l = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  l = __VERIFIER_nondet_int();
  assume_abort_if_not(l <= 1073741823 && n <= 1073741823);
  if (!(l > 0)) {
    result = 0;
    return result;
  }
  k = 1;
  while (k < n) {
    i = l;
    while (i < n) {
      __VERIFIER_assert(1 <= i);
      i = i + 1;
    }
    tmp_1 = __VERIFIER_nondet_int();
    if (tmp_1 != 0) {
      l = l + 1;
    }
    k = k + 1;
  }
}

