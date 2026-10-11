// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-acceleration/phases_2-2.c
// SV-COMP loop-acceleration/phases_2-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/phases_2-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "phases_2-2.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  x = 1;
  y = __VERIFIER_nondet_int();
  assume_abort_if_not(y >= 0);
  if (!(y > 0)) {
    return;
  }
  while (x < y) {
    if (x < y / x) {
      x = x * x;
    } else {
      x = x + 1;
    }
  }
  __VERIFIER_assert(x == y);
}

