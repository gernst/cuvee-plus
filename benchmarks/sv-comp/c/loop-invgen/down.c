// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/down.c
// SV-COMP loop-invgen/down.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/down.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "down.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int n = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  k = 0;
  i = 0;
  n = __VERIFIER_nondet_int();
  while (i < n) {
    i = i + 1;
    k = k + 1;
  }
  j = n;
  while (j > 0) {
    __VERIFIER_assert(k > 0);
    j = j - 1;
    k = k - 1;
  }
}

