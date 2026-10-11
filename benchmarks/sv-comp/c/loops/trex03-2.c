// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/trex03-2.c
// SV-COMP loops/trex03-2.yml, translated from benchmarks/sv-comp/dafny/loops/trex03-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "trex03-2.c", 7, "reach_error"); }
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

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  _Bool tmp_4 = __VERIFIER_nondet_bool();
  _Bool tmp_5 = __VERIFIER_nondet_bool();
  int x1 = __VERIFIER_nondet_int();
  int x2 = __VERIFIER_nondet_int();
  int x3 = __VERIFIER_nondet_int();
  int d1 = __VERIFIER_nondet_int();
  int d2 = __VERIFIER_nondet_int();
  int d3 = __VERIFIER_nondet_int();
  _Bool c1 = __VERIFIER_nondet_bool();
  _Bool c2 = __VERIFIER_nondet_bool();
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  x1 = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_2);
  x2 = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_3);
  x3 = tmp_3;
  d1 = 1;
  d2 = 1;
  d3 = 1;
  tmp_4 = __VERIFIER_nondet_bool();
  c1 = tmp_4;
  tmp_5 = __VERIFIER_nondet_bool();
  c2 = tmp_5;
  while (x1 > 0 && x2 > 0 && x3 > 0) {
    if (c1) {
      x1 = x1 - d1;
    } else if (c2) {
      x2 = x2 - d2;
    } else {
      x3 = x3 - d3;
    }
    c1 = __VERIFIER_nondet_bool();
    c2 = __VERIFIER_nondet_bool();
  }
  __VERIFIER_assert(x1 == 0 || x2 == 0 || x3 == 0);
  result = 0;
  return result;
}

