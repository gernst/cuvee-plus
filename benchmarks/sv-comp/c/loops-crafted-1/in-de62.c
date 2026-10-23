// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops-crafted-1/in-de62.c
// SV-COMP loops-crafted-1/in-de62.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/in-de62.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "in-de62.c", 7, "reach_error"); }
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
  int n = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  n = tmp_1;
  x = n;
  y = 0;
  while (x > 0) {
    x = x - 1;
    y = y + 1;
  }
  z = y;
  while (z > 0) {
    x = x + 1;
    z = z - 1;
  }
  while (y > 0) {
    y = y - 1;
    z = z + 1;
  }
  while (x > 0) {
    x = x - 1;
    y = y + 1;
  }
  while (z > 0) {
    x = x + 1;
    z = z - 1;
  }
  while (y > 0) {
    y = y - 1;
    x = x - 1;
  }
  __VERIFIER_assert(x == 0);
  result = 0;
  return result;
}

