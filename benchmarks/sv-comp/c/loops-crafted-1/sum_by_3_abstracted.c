// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/sum_by_3_abstracted.c
// SV-COMP loops-crafted-1/sum_by_3_abstracted.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/sum_by_3_abstracted.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sum_by_3_abstracted.c", 7, "reach_error"); }
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
  int i = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= n);
  i = 0;
  if (i < n) {
    i = __VERIFIER_nondet_int();
    assume_abort_if_not(0 <= i);
    if (!(i < n)) {
      assume_abort_if_not(0);
    }
    if (i < n) {
      i = i + 1;
    }
    if (i < n) {
      assume_abort_if_not(0);
    }
  }
  j = i;
  while (j < n) {
    j = j + 1;
  }
  k = j;
  while (k < n) {
    k = k + 1;
  }
  __VERIFIER_assert((i + j + k) / 3 <= n);
  result = 0;
  return result;
}

