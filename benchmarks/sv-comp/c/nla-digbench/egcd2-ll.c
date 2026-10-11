// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/egcd2-ll.c
// SV-COMP nla-digbench/egcd2-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/egcd2-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "egcd2-ll.c", 7, "reach_error"); }
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
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int p = __VERIFIER_nondet_int();
  int q = __VERIFIER_nondet_int();
  int r = __VERIFIER_nondet_int();
  int s = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int xy = __VERIFIER_nondet_int();
  int yy = __VERIFIER_nondet_int();
  int temp = __VERIFIER_nondet_int();
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  assume_abort_if_not(x >= 1);
  assume_abort_if_not(y >= 1);
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;
  c = 0;
  k = 0;
  xy = x * y;
  yy = y * y;
  while (1 != 0) {
    if (!(b != 0)) {
      break;
    }
    c = a;
    k = 0;
    while (1 != 0) {
      __VERIFIER_assert(a == k * b + c);
      __VERIFIER_assert(a == y * r + x * p);
      __VERIFIER_assert(b == x * q + y * s);
      __VERIFIER_assert(q * xy + s * yy - q * x - b * y - s * y + b == 0);
      if (!(c >= b)) {
        break;
      }
      c = c - b;
      k = k + 1;
    }
    a = b;
    b = c;
    temp = p;
    p = q;
    q = temp - q * k;
    temp = r;
    r = s;
    s = temp - s * k;
  }
  __VERIFIER_assert(q * x + s * y == 0);
  __VERIFIER_assert(p * x + r * y == a);
  result = a;
  return result;
}

