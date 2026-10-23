// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-invariants/eq1.c
// SV-COMP loop-invariants/eq1.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/eq1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "eq1.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int w = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  w = __VERIFIER_nondet_int();
  x = w;
  y = __VERIFIER_nondet_int();
  z = y;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    c = __VERIFIER_nondet_int();
    if (c != 0) {
      w = w + 1;
      x = x + 1;
    } else {
      y = y - 1;
      z = z - 1;
    }
    b = __VERIFIER_nondet_int();
  }
  __VERIFIER_assert(w == x && y == z);
}

