// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-lit/jm2006_variant.c
// SV-COMP loop-lit/jm2006_variant.yml, translated from benchmarks/sv-comp/dafny/loop-lit/jm2006_variant.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "jm2006_variant.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  i = __VERIFIER_nondet_int();
  j = __VERIFIER_nondet_int();
  if (!(i >= 0)) {
    return;
  }
  if (!(j >= 0)) {
    return;
  }
  x = i;
  y = j;
  z = 0;
  while (x != 0) {
    x = x - 1;
    y = y - 2;
    z = z + 1;
  }
  if (i == j) {
    __VERIFIER_assert(y == -z);
  }
}

