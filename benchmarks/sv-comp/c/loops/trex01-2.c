// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/trex01-2.c
// SV-COMP loops/trex01-2.yml, translated from benchmarks/sv-comp/dafny/loops/trex01-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "trex01-2.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void f(int d) {
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  _Bool tmp_4 = __VERIFIER_nondet_bool();
  _Bool tmp_5 = __VERIFIER_nondet_bool();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  _Bool c = __VERIFIER_nondet_bool();
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  y = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  k = tmp_3;
  z = 1;
  while (z < k) {
    z = 2 * z;
  }
  __VERIFIER_assert(z >= 1);
  while (x > 0 && y > 0) {
    tmp_4 = __VERIFIER_nondet_bool();
    c = tmp_4;
    if (c) {
      x = x - d;
      tmp_5 = __VERIFIER_nondet_bool();
      y = tmp_5 ? 1 : 0;
      z = z - 1;
    } else {
      y = y - d;
    }
  }
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  _Bool tmp_6 = __VERIFIER_nondet_bool();
  _Bool c = __VERIFIER_nondet_bool();
  tmp_6 = __VERIFIER_nondet_bool();
  c = tmp_6;
  if (c) {
    f(1);
  } else {
    f(2);
  }
  result = 0;
  return result;
}

