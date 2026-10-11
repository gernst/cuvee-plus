// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/vnew1.c
// SV-COMP loops-crafted-1/vnew1.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/vnew1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "vnew1.c", 7, "reach_error"); }
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

void main(void) {
  int n = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= n);
  k = n;
  i = 0;
  while (i < n) {
    k = k - 1;
    i = i + 3;
  }
  j = 0;
  while (j < n / 3) {
    __VERIFIER_assert(k > 0);
    k = k - 1;
    j = j + 1;
  }
}

