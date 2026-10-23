// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/nla-digbench/egcd3-ll.c
// SV-COMP nla-digbench/egcd3-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/egcd3-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "egcd3-ll.c", 7, "reach_error"); }
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
  int temp = __VERIFIER_nondet_int();
  int d = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
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
  while (1 != 0) {
    if (!(b != 0)) {
      break;
    }
    c = a;
    k = 0;
    while (1 != 0) {
      if (!(c >= b)) {
        break;
      }
      d = 1;
      v = b;
      while (1 != 0) {
        __VERIFIER_assert(a == y * r + x * p);
        __VERIFIER_assert(b == x * q + y * s);
        __VERIFIER_assert(a == k * b + c);
        __VERIFIER_assert(v == b * d);
        if (!(c >= 2 * v)) {
          break;
        }
        d = 2 * d;
        v = 2 * v;
      }
      c = c - v;
      k = k + d;
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
  __VERIFIER_assert(p * x - q * x + r * y - s * y == a);
  result = 0;
  return result;
}

