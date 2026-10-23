// ./Cuvee.sh -teq -prove -split -prove benchmarks/sv-comp/c/loop-invgen/seq-3.c
// SV-COMP loop-invgen/seq-3.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/seq-3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "seq-3.c", 7, "reach_error"); }
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
  int n0 = __VERIFIER_nondet_int();
  int n1 = __VERIFIER_nondet_int();
  int i0 = __VERIFIER_nondet_int();
  int i1 = __VERIFIER_nondet_int();
  int j1 = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  i0 = 0;
  k = 0;
  n0 = __VERIFIER_nondet_int();
  n1 = __VERIFIER_nondet_int();
  while (i0 < n0) {
    i0 = i0 + 1;
    k = k + 1;
  }
  i1 = 0;
  while (i1 < n1) {
    i1 = i1 + 1;
    k = k + 1;
  }
  j1 = 0;
  while (j1 < n0 + n1) {
    __VERIFIER_assert(k > 0);
    j1 = j1 + 1;
    k = k - 1;
  }
}

