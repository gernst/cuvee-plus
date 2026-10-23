// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops-crafted-1/mono-crafted_12.c
// SV-COMP loops-crafted-1/mono-crafted_12.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_12.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "mono-crafted_12.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  x = 0;
  y = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < y);
  z = 0;
  while (x < y) {
    if (x >= 5000000) {
      z = z + 2;
    }
    x = x + 1;
  }
  __VERIFIER_assert(!(z % 2 != 0));
  result = 0;
  return result;
}

