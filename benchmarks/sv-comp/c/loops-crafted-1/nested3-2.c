// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/nested3-2.c
// SV-COMP loops-crafted-1/nested3-2.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/nested3-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested3-2.c", 7, "reach_error"); }
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
  int N = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  int w = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  x = 0;
  y = 0;
  z = 0;
  w = 0;
  while (x < N) {
    y = 0;
    while (y < N) {
      z = 0;
      while (z < N) {
        z = z + 1;
      }
      __VERIFIER_assert(!(z % 4 != 0));
      y = y + 1;
    }
    __VERIFIER_assert(!(y % 2 != 0));
    x = x + 1;
  }
  __VERIFIER_assert(!(x % 2 != 0));
  result = 0;
  return result;
}

