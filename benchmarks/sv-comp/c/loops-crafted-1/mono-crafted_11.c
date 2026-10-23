// ./Cuvee.sh -teq -prove -split -prove benchmarks/sv-comp/c/loops-crafted-1/mono-crafted_11.c
// SV-COMP loops-crafted-1/mono-crafted_11.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/mono-crafted_11.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "mono-crafted_11.c", 7, "reach_error"); }
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
  int K = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < K);
  assume_abort_if_not(N == 20 * K);
  x = 0;
  while (x < N) {
    if (x < 2 * K) {
      x = x + 1;
    } else {
      x = x + 2;
    }
  }
  __VERIFIER_assert(x % 2 == 0);
  result = 0;
  return result;
}

