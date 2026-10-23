// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-invgen/string_concat-noarr.c
// SV-COMP loop-invgen/string_concat-noarr.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/string_concat-noarr.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "string_concat-noarr.c", 7, "reach_error"); }
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
  int b = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  i = 0;
  b = __VERIFIER_nondet_int();
  while (b != 0 && i < N) {
    i = i + 1;
    b = __VERIFIER_nondet_int();
  }
  if (i >= 100) {
    assume_abort_if_not(0);
  }
  j = 0;
  b = __VERIFIER_nondet_int();
  while (b != 0 && i < N) {
    i = i + 1;
    j = j + 1;
    b = __VERIFIER_nondet_int();
  }
  if (j >= 100) {
    assume_abort_if_not(0);
  }
  __VERIFIER_assert(i < 200);
}

