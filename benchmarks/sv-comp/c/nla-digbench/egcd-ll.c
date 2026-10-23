// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/nla-digbench/egcd-ll.c
// SV-COMP nla-digbench/egcd-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/egcd-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "egcd-ll.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int p = __VERIFIER_nondet_int();
  int q = __VERIFIER_nondet_int();
  int r = __VERIFIER_nondet_int();
  int s = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
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
    __VERIFIER_assert(1 == p * s - r * q);
    __VERIFIER_assert(a == y * r + x * p);
    __VERIFIER_assert(b == x * q + y * s);
    if (!(a != b)) {
      break;
    }
    if (a > b) {
      a = a - b;
      p = p - q;
      r = r - s;
    } else {
      b = b - a;
      q = q - p;
      s = s - r;
    }
  }
  __VERIFIER_assert(a - b == 0);
  __VERIFIER_assert(p * x + r * y - b == 0);
  __VERIFIER_assert(q * r - p * s + 1 == 0);
  __VERIFIER_assert(q * x + s * y - b == 0);
  result = 0;
  return result;
}

