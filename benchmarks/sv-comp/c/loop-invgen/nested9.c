// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-invgen/nested9.c
// SV-COMP loop-invgen/nested9.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/nested9.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested9.c", 7, "reach_error"); }
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

int __BLAST_NONDET;

int main(void) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int l = __VERIFIER_nondet_int();
  int m = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  m = __VERIFIER_nondet_int();
  l = __VERIFIER_nondet_int();
  if (3 * n <= m + l) {} else {
    result = 0;
    return result;
  }
  i = 0;
  while (i < n) {
    j = 2 * i;
    while (j < 3 * i) {
      k = i;
      while (k < j) {
        __VERIFIER_assert(k - i <= 2 * n);
        k = k + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

