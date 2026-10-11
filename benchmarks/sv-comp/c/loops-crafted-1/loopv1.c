// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/loopv1.c
// SV-COMP loops-crafted-1/loopv1.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/loopv1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "loopv1.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int n = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  i = 0;
  j = 0;
  while (i < n) {
    c = __VERIFIER_nondet_int();
    if (c != 0) {
      i = i + 6;
    } else {
      i = i + 3;
    }
  }
  __VERIFIER_assert(i % 3 == 0);
}

