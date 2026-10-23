// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-zilu/benchmark43_conjunctive_abstracted.c
// SV-COMP loop-zilu/benchmark43_conjunctive_abstracted.yml, translated from benchmarks/sv-comp/dafny/loop-zilu/benchmark43_conjunctive_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "benchmark43_conjunctive_abstracted.c", 7, "reach_error"); }
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
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  y = tmp_2;
  if (!(x < 100 && y < 100)) {
    result = 0;
    return result;
  }
  if (((y < 100 ? 1 : 0) & (x < 100 ? 1 : 0)) != 0) {
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    if (!(((y < 100 ? 1 : 0) & (x < 100 ? 1 : 0)) != 0)) {
      assume_abort_if_not(0);
    }
    if (x < 100 && y < 100) {
      x = x + 1;
      y = y + 1;
    }
    if (((y < 100 ? 1 : 0) & (x < 100 ? 1 : 0)) != 0) {
      assume_abort_if_not(0);
    }
  }
  __VERIFIER_assert(x == 100 || y == 100);
  result = 0;
  return result;
}

