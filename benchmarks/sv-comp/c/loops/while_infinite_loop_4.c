// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/while_infinite_loop_4.c
// SV-COMP loops/while_infinite_loop_4.yml, translated from benchmarks/sv-comp/dafny/loops/while_infinite_loop_4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "while_infinite_loop_4.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int x;

void eval(void) {
  while (1 != 0) {
    x = 1;
    break;
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  x = 0;
  while (1 != 0) {
    eval();
    __VERIFIER_assert(x == 0);
  }
  __VERIFIER_assert(x == 0);
  result = 0;
  return result;
}

