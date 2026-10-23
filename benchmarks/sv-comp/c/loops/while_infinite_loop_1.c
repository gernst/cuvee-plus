// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops/while_infinite_loop_1.c
// SV-COMP loops/while_infinite_loop_1.yml, translated from benchmarks/sv-comp/dafny/loops/while_infinite_loop_1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "while_infinite_loop_1.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  x = 0;
  while (1 != 0) {
    __VERIFIER_assert(x == 0);
  }
  __VERIFIER_assert(x != 0);
}

