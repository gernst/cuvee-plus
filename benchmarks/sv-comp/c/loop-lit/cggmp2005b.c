// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-lit/cggmp2005b.c
// SV-COMP loop-lit/cggmp2005b.yml, translated from benchmarks/sv-comp/dafny/loop-lit/cggmp2005b.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "cggmp2005b.c", 7, "reach_error"); }
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
  int N = __VERIFIER_nondet_int();
  int M = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  assume_abort_if_not(0 < M);
  i = 0;
  k = 9;
  j = -N;
  while (i <= N) {
    i = i + 1;
    while (j < M) {
      j = i + j;
    }
    k = 4;
    while (k <= 3) {
      k = k + 1;
    }
  }
  __VERIFIER_assert(k == 4);
  result = 0;
  return result;
}

