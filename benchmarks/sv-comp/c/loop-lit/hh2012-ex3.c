// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-lit/hh2012-ex3.c
// SV-COMP loop-lit/hh2012-ex3.yml, translated from benchmarks/sv-comp/dafny/loop-lit/hh2012-ex3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "hh2012-ex3.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  i = 0;
  while (i < 4) {
    j = 0;
    while (j < 4) {
      i = i + 1;
      j = j + 1;
      __VERIFIER_assert(0 <= j);
      __VERIFIER_assert(j <= i);
      __VERIFIER_assert(i <= j + 3);
      __VERIFIER_assert(j <= 4);
    }
    __VERIFIER_assert(0 <= j);
    __VERIFIER_assert(j <= i);
    __VERIFIER_assert(i <= j + 3);
    __VERIFIER_assert(j <= 4);
    i = i - j + 1;
  }
  result = 0;
  return result;
}

