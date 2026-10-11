// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/nested6.c
// SV-COMP loop-invgen/nested6.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/nested6.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested6.c", 7, "reach_error"); }
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
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  if (k == n) {} else {
    result = 0;
    return result;
  }
  i = 0;
  while (i < n) {
    j = 2 * i;
    while (j < n) {
      tmp_1 = __VERIFIER_nondet_int();
      if (tmp_1 != 0) {
        k = j;
        while (k < n) {
          __VERIFIER_assert(k >= 2 * i);
          k = k + 1;
        }
      } else {
        __VERIFIER_assert(k >= n);
        __VERIFIER_assert(k <= n);
      }
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

