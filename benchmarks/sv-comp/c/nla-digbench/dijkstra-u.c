// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/nla-digbench/dijkstra-u.c
// SV-COMP nla-digbench/dijkstra-u.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/dijkstra-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "dijkstra-u.c", 7, "reach_error"); }
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
  int n = __VERIFIER_nondet_int();
  int p = __VERIFIER_nondet_int();
  int q = __VERIFIER_nondet_int();
  int r = __VERIFIER_nondet_int();
  int h = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= n);
  p = 0;
  q = 1;
  r = n;
  h = 0;
  while (1 != 0) {
    if (!(q <= n)) {
      break;
    }
    q = 4 * q;
  }
  while (1 != 0) {
    __VERIFIER_assert(r < 2 * p + q);
    __VERIFIER_assert(p * p + r * q == n * q);
    __VERIFIER_assert(
      h * h * h - 12 * h * n * q + 16 * n * p * q - h * q * q - 4 * p * q * q
        + 12 * h * q * r
        - 16 * p * q * r
        == 0);
    __VERIFIER_assert(
      h * h * n - 4 * h * n * p + 4 * (n * n) * q - n * q * q - h * h * r
        + 4 * h * p * r
        - 8 * n * q * r
        + q * q * r
        + 4 * q * r * r
        == 0);
    __VERIFIER_assert(
      h * h * p - 4 * h * n * q + 4 * n * p * q - p * q * q + 4 * h * q * r
        - 4 * p * q * r
        == 0);
    __VERIFIER_assert(p * p - n * q + q * r == 0);
    if (!(q != 1)) {
      break;
    }
    q = q / 4;
    h = p + q;
    p = p / 2;
    if (r >= h) {
      p = p + q;
      r = r - h;
    }
  }
  __VERIFIER_assert(
    h * h * h - 12 * h * n + 16 * n * p + 12 * h * r - 16 * p * r - h - 4 * p
      == 0);
  __VERIFIER_assert(p * p - n + r == 0);
  __VERIFIER_assert(h * h * p - 4 * h * n + 4 * n * p + 4 * h * r - 4 * p * r - p == 0);
  result = 0;
  return result;
}

