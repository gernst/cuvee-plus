// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/functions_1-2.c
// SV-COMP loop-acceleration/functions_1-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/functions_1-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "functions_1-2.c", 7, "reach_error"); }
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

int f(int z) {
  int result = __VERIFIER_nondet_int();
  result = z + 2;
  return result;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  x = 0;
  while (x < N) {
    x = f(x);
  }
  __VERIFIER_assert(x % 2 != 0);
}

