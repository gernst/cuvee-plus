// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops/trex04_abstracted.c
// SV-COMP loops/trex04_abstracted.yml, translated from benchmarks/sv-comp/dafny/loops/trex04_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "trex04_abstracted.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
void assume_abort_if_not(int cond) {
  if (!cond) { abort(); }
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void foo(void) {
  _Bool tmp_1 = __VERIFIER_nondet_bool();
  _Bool tmp_2 = __VERIFIER_nondet_bool();
  int y = __VERIFIER_nondet_int();
  _Bool c1 = __VERIFIER_nondet_bool();
  _Bool c2 = __VERIFIER_nondet_bool();
  y = 0;
  tmp_1 = __VERIFIER_nondet_bool();
  c1 = tmp_1;
  tmp_2 = __VERIFIER_nondet_bool();
  c2 = tmp_2;
  if (c1) {
    y = y + 1;
  }
  if (c2) {
    y = y - 1;
  } else {
    y = y + 10;
  }
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  _Bool tmp_4 = __VERIFIER_nondet_bool();
  _Bool tmp_5 = __VERIFIER_nondet_bool();
  int d = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  _Bool c1 = __VERIFIER_nondet_bool();
  _Bool c2 = __VERIFIER_nondet_bool();
  d = 1;
  tmp_3 = __VERIFIER_nondet_int();
  x = tmp_3;
  tmp_4 = __VERIFIER_nondet_bool();
  c1 = tmp_4;
  tmp_5 = __VERIFIER_nondet_bool();
  c2 = tmp_5;
  if (c1) {
    d = d - 1;
  }
  if (c2) {
    foo();
  }
  c1 = __VERIFIER_nondet_bool();
  c2 = __VERIFIER_nondet_bool();
  if (c1) {
    foo();
  }
  if (c2) {
    d = d - 1;
  }
  if (x > 0) {
    x = __VERIFIER_nondet_int();
  }
  if (x > 0) {
    assume_abort_if_not(0);
  }
  __VERIFIER_assert(x <= 0);
}

