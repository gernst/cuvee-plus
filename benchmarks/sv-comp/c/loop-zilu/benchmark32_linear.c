// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-zilu/benchmark32_linear.c
// SV-COMP loop-zilu/benchmark32_linear.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark32_linear.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark32_linear.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  _Bool tmp_2 = __VERIFIER_nondet_bool();
  int x = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  if (!(x == 1 || x == 2)) {
    result = 0;
    return result;
  }
  while (1) {
    tmp_2 = __VERIFIER_nondet_bool();
    if (!tmp_2) {
      break;
    }
    if (x == 1) {
      x = 2;
    } else if (x == 2) {
      x = 1;
    }
  }
  __VERIFIER_assert(x <= 8);
  result = 0;
  return result;
}

