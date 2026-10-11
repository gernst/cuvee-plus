// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/ps5-ll.c
// SV-COMP nla-digbench/ps5-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/ps5-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "ps5-ll.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();
  y = 0;
  x = 0;
  c = 0;
  while (1 != 0) {
    __VERIFIER_assert(
      6 * y * y * y * y * y + 15 * y * y * y * y + 10 * y * y * y - 30 * x - y
        == 0);
    if (!(c < k)) {
      break;
    }
    c = c + 1;
    y = y + 1;
    x = y * y * y * y + x;
  }
  __VERIFIER_assert(
    6 * y * y * y * y * y + 15 * y * y * y * y + 10 * y * y * y - 30 * x - y
      == 0);
  __VERIFIER_assert(k * y == y * y);
  result = 0;
  return result;
}

