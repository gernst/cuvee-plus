// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-invgen/large_const.c
// SV-COMP loop-invgen/large_const.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/large_const.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "large_const.c", 7, "reach_error"); }
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

void main(void) {
  int c1 = __VERIFIER_nondet_int();
  int c2 = __VERIFIER_nondet_int();
  int c3 = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  c1 = 4000;
  c2 = 2000;
  c3 = 10000;
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= n && n < 10);
  k = 0;
  i = 0;
  while (i < n) {
    i = i + 1;
    v = __VERIFIER_nondet_int();
    assume_abort_if_not(0 <= v && n < 2);
    if (v == 0) {
      k = k + c1;
    } else if (v == 1) {
      k = k + c2;
    } else {
      k = k + c3;
    }
  }
  j = 0;
  while (j < n) {
    __VERIFIER_assert(k > 0);
    j = j + 1;
    k = k - 1;
  }
}

