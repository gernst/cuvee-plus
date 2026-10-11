// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/mannadiv.c
// SV-COMP nla-digbench/mannadiv.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/mannadiv.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "mannadiv.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void assume_abort_if_not(int cond) {
  if (!(cond != 0)) {
    assume_abort_if_not(0);
  }
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int x1 = __VERIFIER_nondet_int();
  int x2 = __VERIFIER_nondet_int();
  int y1 = __VERIFIER_nondet_int();
  int y2 = __VERIFIER_nondet_int();
  int y3 = __VERIFIER_nondet_int();
  x1 = __VERIFIER_nondet_int();
  x2 = __VERIFIER_nondet_int();
  assume_abort_if_not(x1 >= 0 ? 1 : 0);
  assume_abort_if_not(x2 != 0 ? 1 : 0);
  y1 = 0;
  y2 = 0;
  y3 = x1;
  while (1 != 0) {
    __VERIFIER_assert(y1 * x2 + y2 + y3 == x1);
    if (!(y3 != 0)) {
      break;
    }
    if (y2 + 1 == x2) {
      y1 = y1 + 1;
      y2 = 0;
      y3 = y3 - 1;
    } else {
      y2 = y2 + 1;
      y3 = y3 - 1;
    }
  }
  __VERIFIER_assert(y1 * x2 + y2 == x1);
  result = 0;
  return result;
}

