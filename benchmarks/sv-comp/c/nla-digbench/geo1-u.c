// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/geo1-u.c
// SV-COMP nla-digbench/geo1-u.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/geo1-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "geo1-u.c", 7, "reach_error"); }
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
  int z = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  z = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= z);
  k = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= k);
  x = 1;
  y = z;
  c = 1;
  while (1 != 0) {
    __VERIFIER_assert(x * z - x - y + 1 == 0);
    if (!(c < k)) {
      break;
    }
    c = c + 1;
    x = x * z + 1;
    y = y * z;
  }
  x = x * (z - 1);
  __VERIFIER_assert(1 + x - y == 0);
  result = 0;
  return result;
}

