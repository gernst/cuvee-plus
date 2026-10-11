// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-simple/nested_1b.c
// SV-COMP loop-simple/nested_1b.yml, translated from benchmarks/sv-comp/dafny/loop-simple/nested_1b.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested_1b.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  a = 6;
  a = 0;
  while (a < 6) {
    a = a + 1;
  }
  if (a == 6) {
    __VERIFIER_assert(0);
  }
  result = 1;
  return result;
}

