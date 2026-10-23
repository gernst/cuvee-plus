// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-lit/bhmr2007.c
// SV-COMP loop-lit/bhmr2007.yml, translated from benchmarks/sv-comp/dafny/loop-lit/bhmr2007.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "bhmr2007.c", 7, "reach_error"); }
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
  int n = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  i = 0;
  a = 0;
  b = 0;
  n = __VERIFIER_nondet_int();
  if (!(n >= 0)) {
    result = 0;
    return result;
  }
  while (i < n) {
    tmp_1 = __VERIFIER_nondet_int();
    if (tmp_1 != 0) {
      a = a + 1;
      b = b + 2;
    } else {
      a = a + 2;
      b = b + 1;
    }
    i = i + 1;
  }
  __VERIFIER_assert(a + b == 3 * n);
  result = 0;
  return result;
}

