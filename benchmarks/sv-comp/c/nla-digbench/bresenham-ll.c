// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/bresenham-ll.c
// SV-COMP nla-digbench/bresenham-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/bresenham-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "bresenham-ll.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int X = __VERIFIER_nondet_int();
  int Y = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  int xy = __VERIFIER_nondet_int();
  int yx = __VERIFIER_nondet_int();
  X = __VERIFIER_nondet_int();
  Y = __VERIFIER_nondet_int();
  v = 2 * Y - X;
  y = 0;
  x = 0;
  while (1 != 0) {
    yx = Y * x;
    xy = X * y;
    __VERIFIER_assert(2 * yx - 2 * xy - X + 2 * Y - v == 0);
    if (!(x <= X)) {
      break;
    }
    if (v < 0) {
      v = v + 2 * Y;
    } else {
      v = v + 2 * (Y - X);
      y = y + 1;
    }
    x = x + 1;
  }
  xy = x * y;
  yx = Y * x;
  __VERIFIER_assert(2 * yx - 2 * xy - X + 2 * Y - v + 2 * y == 0);
  result = 0;
  return result;
}

