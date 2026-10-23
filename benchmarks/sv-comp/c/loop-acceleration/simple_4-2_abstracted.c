// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-acceleration/simple_4-2_abstracted.c
// SV-COMP loop-acceleration/simple_4-2_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_4-2_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "simple_4-2_abstracted.c", 7, "reach_error"); }
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
  x = 268435440;
  if (x > 0) {
    x = __VERIFIER_nondet_int();
    assume_abort_if_not(0 <= x);
  }
  if (x > 0) {
    assume_abort_if_not(0);
  }
  __VERIFIER_assert(!(x % 2 != 0));
}

