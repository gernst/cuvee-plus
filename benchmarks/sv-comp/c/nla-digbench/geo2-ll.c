// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/nla-digbench/geo2-ll.c
// SV-COMP nla-digbench/geo2-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/geo2-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "geo2-ll.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
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
  k = __VERIFIER_nondet_int();
  x = 1;
  y = 1;
  c = 1;
  while (1 != 0) {
    __VERIFIER_assert(1 + x * z - x - z * y == 0);
    if (!(c < k)) {
      break;
    }
    c = c + 1;
    x = x * z + 1;
    y = y * z;
  }
  __VERIFIER_assert(1 + x * z - x - z * y == 0);
  result = 0;
  return result;
}

