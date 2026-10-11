// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/iftelse.c
// SV-COMP loops-crafted-1/iftelse.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/iftelse.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "iftelse.c", 7, "reach_error"); }
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
  k = 0;
  j = k;
  i = j;
  while (i < n) {
    i = i + 3;
    if (i % 2 != 0) {
      j = j + 3;
    } else {
      k = k + 3;
    }
    if (n > 0) {
      __VERIFIER_assert(i / 2 <= j);
    }
  }
  result = 0;
  return result;
}

