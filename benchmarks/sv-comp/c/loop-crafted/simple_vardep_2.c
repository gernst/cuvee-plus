// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-crafted/simple_vardep_2.c
// SV-COMP loop-crafted/simple_vardep_2.yml, translated from benchmarks/sv-comp/dafny/loop-crafted/simple_vardep_2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "simple_vardep_2.c", 7, "reach_error"); }
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
  int N = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  i = 0;
  j = 0;
  k = 0;
  while (k < N) {
    i = i + 1;
    j = j + 2;
    k = k + 3;
    __VERIFIER_assert(k == 3 * i && j == 2 * i);
  }
}

