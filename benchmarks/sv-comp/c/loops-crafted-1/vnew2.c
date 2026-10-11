// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/vnew2.c
// SV-COMP loops-crafted-1/vnew2.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/vnew2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "vnew2.c", 7, "reach_error"); }
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
  int n = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= n);
  k = 0;
  j = k;
  i = j;
  while (i < n) {
    i = i + 3;
    j = j + 3;
    k = k + 3;
  }
  if (n > 0) {
    __VERIFIER_assert(i == j && j == k && i % (n + 3) != 0);
  }
  result = 0;
  return result;
}

